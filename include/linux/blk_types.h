/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Block data types and constants.  Directly include this file only to
 * break include dependency loop.
 */
#ifndef __LINUX_BLK_TYPES_H
#define __LINUX_BLK_TYPES_H

#include <linux/types.h>
#include <linux/bvec.h>
#include <linux/ktime.h>

struct bio_set;
struct bio;
struct bio_integrity_payload;
struct page;
struct io_context;
struct cgroup_subsys_state;
typedef void (bio_end_io_t) (struct bio *);
struct bio_crypt_ctx;

struct block_device {
	dev_t			bd_dev;
	int			bd_openers;
	struct inode *		bd_inode;	/* will die */
	struct super_block *	bd_super;
	struct mutex		bd_mutex;	/* open/close mutex */
	void *			bd_claiming;
	void *			bd_holder;
	int			bd_holders;
	bool			bd_write_holder;
#ifdef CONFIG_SYSFS
	struct list_head	bd_holder_disks;
#endif
	struct block_device *	bd_contains;
	u8			bd_partno;
	struct hd_struct *	bd_part;
	/* number of times partitions within this device have been opened. */
	unsigned		bd_part_count;

	spinlock_t		bd_size_lock; /* for bd_inode->i_size updates */
	struct gendisk *	bd_disk;
	struct backing_dev_info *bd_bdi;

	/* The counter of freeze processes */
	int			bd_fsfreeze_count;
	/* Mutex for freeze */
	struct mutex		bd_fsfreeze_mutex;
} __randomize_layout;

/*
 * Block error status values.  See block/blk-core:blk_errors for the details.
 * Alpha cannot write a byte atomically, so we need to use 32-bit value.
 */
#if defined(CONFIG_ALPHA) && !defined(__alpha_bwx__)
typedef u32 __bitwise blk_status_t;
#else
typedef u8 __bitwise blk_status_t;
#endif
#define	BLK_STS_OK 0
#define BLK_STS_NOTSUPP		((__force blk_status_t)1)
#define BLK_STS_TIMEOUT		((__force blk_status_t)2)
#define BLK_STS_NOSPC		((__force blk_status_t)3)
#define BLK_STS_TRANSPORT	((__force blk_status_t)4)
#define BLK_STS_TARGET		((__force blk_status_t)5)
#define BLK_STS_NEXUS		((__force blk_status_t)6)
#define BLK_STS_MEDIUM		((__force blk_status_t)7)
#define BLK_STS_PROTECTION	((__force blk_status_t)8)
#define BLK_STS_RESOURCE	((__force blk_status_t)9)
#define BLK_STS_IOERR		((__force blk_status_t)10)

/* hack for device mapper, don't use elsewhere: */
#define BLK_STS_DM_REQUEUE    ((__force blk_status_t)11)

#define BLK_STS_AGAIN		((__force blk_status_t)12)

/*
 * BLK_STS_DEV_RESOURCE is returned from the driver to the block layer if
 * device related resources are unavailable, but the driver can guarantee
 * that the queue will be rerun in the future once resources become
 * available again. This is typically the case for device specific
 * resources that are consumed for IO. If the driver fails allocating these
 * resources, we know that inflight (or pending) IO will free these
 * resource upon completion.
 *
 * This is different from BLK_STS_RESOURCE in that it explicitly references
 * a device specific resource. For resources of wider scope, allocation
 * failure can happen without having pending IO. This means that we can't
 * rely on request completions freeing these resources, as IO may not be in
 * flight. Examples of that are kernel memory allocations, DMA mappings, or
 * any other system wide resources.
 */
#define BLK_STS_DEV_RESOURCE	((__force blk_status_t)13)

/*
 * BLK_STS_ZONE_RESOURCE is returned from the driver to the block layer if zone
 * related resources are unavailable, but the driver can guarantee the queue
 * will be rerun in the future once the resources become available again.
 *
 * This is different from BLK_STS_DEV_RESOURCE in that it explicitly references
 * a zone specific resource and IO to a different zone on the same device could
 * still be served. Examples of that are zones that are write-locked, but a read
 * to the same zone could be served.
 */
#define BLK_STS_ZONE_RESOURCE	((__force blk_status_t)14)

/*
 * BLK_STS_ZONE_OPEN_RESOURCE is returned from the driver in the completion
 * path if the device returns a status indicating that too many zone resources
 * are currently open. The same command should be successful if resubmitted
 * after the number of open zones decreases below the device's limits, which is
 * reported in the request_queue's max_open_zones.
 */
#define BLK_STS_ZONE_OPEN_RESOURCE	((__force blk_status_t)15)

/*
 * BLK_STS_ZONE_ACTIVE_RESOURCE is returned from the driver in the completion
 * path if the device returns a status indicating that too many zone resources
 * are currently active. The same command should be successful if resubmitted
 * after the number of active zones decreases below the device's limits, which
 * is reported in the request_queue's max_active_zones.
 */
#define BLK_STS_ZONE_ACTIVE_RESOURCE	((__force blk_status_t)16)

/**
 * blk_path_error - returns true if error may be path related
 * @error: status the request was completed with
 *
 * Description:
 *     This classifies block error status into non-retryable errors and ones
 *     that may be successful if retried on a failover path.
 *
 * Return:
 *     %false - retrying failover path will not help
 *     %true  - may succeed if retried
 */
static inline bool blk_path_error(blk_status_t error)
{
	switch (error) {
	case BLK_STS_NOTSUPP:
	case BLK_STS_NOSPC:
	case BLK_STS_TARGET:
	case BLK_STS_NEXUS:
	case BLK_STS_MEDIUM:
	case BLK_STS_PROTECTION:
		return false;
	}

	/* Anything else could be a path failure, so should be retried */
	return true;
}

/*
 * From most significant bit:
 * 1 bit: reserved for other usage, see below
 * 12 bits: original size of bio
 * 51 bits: issue time of bio
 */
#define BIO_ISSUE_RES_BITS      1
#define BIO_ISSUE_SIZE_BITS     12
#define BIO_ISSUE_RES_SHIFT     (64 - BIO_ISSUE_RES_BITS)
#define BIO_ISSUE_SIZE_SHIFT    (BIO_ISSUE_RES_SHIFT - BIO_ISSUE_SIZE_BITS)
#define BIO_ISSUE_TIME_MASK     ((1ULL << BIO_ISSUE_SIZE_SHIFT) - 1)
#define BIO_ISSUE_SIZE_MASK     \
	(((1ULL << BIO_ISSUE_SIZE_BITS) - 1) << BIO_ISSUE_SIZE_SHIFT)
#define BIO_ISSUE_RES_MASK      (~((1ULL << BIO_ISSUE_RES_SHIFT) - 1))

/* Reserved bit for blk-throtl */
#define BIO_ISSUE_THROTL_SKIP_LATENCY (1ULL << 63)

struct bio_issue {
	u64 value;
};

static inline u64 __bio_issue_time(u64 time)
{
	return time & BIO_ISSUE_TIME_MASK;
}

static inline u64 bio_issue_time(struct bio_issue *issue)
{
	return __bio_issue_time(issue->value);
}

static inline sector_t bio_issue_size(struct bio_issue *issue)
{
	return ((issue->value & BIO_ISSUE_SIZE_MASK) >> BIO_ISSUE_SIZE_SHIFT);
}

static inline void bio_issue_init(struct bio_issue *issue,
				       sector_t size)
{
	size &= (1ULL << BIO_ISSUE_SIZE_BITS) - 1;
	issue->value = ((issue->value & BIO_ISSUE_RES_MASK) |
			(ktime_get_ns() & BIO_ISSUE_TIME_MASK) |
			((u64)size << BIO_ISSUE_SIZE_SHIFT));
}

/*
 * main unit of I/O for the block layer and lower layers (ie drivers and
 * stacking drivers)
 */
struct bio {
	/* 若一个req中包含多个bio，这些bio通过bi_next组成单向链表，链表以NULL结尾。（bio
	 * merge导致一个req中存在多个bio，如果没有merge，一个bio对应一个req） */
	struct bio		*bi_next;	/* request queue link */
	/* bio待操作的存储设备（linux块设备代码用struct gendisk描述一个实际的disk）*/
	struct gendisk		*bi_disk;
	/* 高8位表示operation，范围0~255，代码中用REQ_OP_XX表示某个operation，如REQ_OP_READ。
	 * 低24表示flag，每个bit对应一个flag，代码中用REQ_xx表示某个flag，如REQ_SYNC。*/
	unsigned int		bi_opf;		/* bottom bits req flags,
						 * top bits REQ_OP. Use
						 * accessors.
						 */

	/* 高3位表示bio->bi_io_vec指向的内存空间是从哪个bvec pool中分配的（这块空间中存放了多个struct
	 * bio_vec），代码中一共定义了BVEC_POOL_NR（值为6）个bvec pool见数组 struct biovec_slab bvec_slabs[BVEC_POOL_NR]
	 *
	 * 低13位表示bio的标记，值范围0~2^13，用BIO_XX表示，如BIO_CHAIN表示该bio是bio
	 * chain中的一个（bio拆分后或者md驱动中，多个bio形成bio chain）*/
	unsigned short		bi_flags;	/* status, etc and bvec pool number */

	/* io优先级，IOPRIO_CLASS_XX（其中XX为NONE、RT、BE、IDLE）.并不是所有io调度器都会用到这个变量。
	 * io调度器（如bfq）针对不同优先级io的行为是不一样的。在bio merge或req merge时，不同的优先级的
	 * bio或req不允许merge。*/
	unsigned short		bi_ioprio;

	/* 描述bio待写数据的life time属性，代码中用WRITE_LIFE_XX表示（其中XX为NOT_SET、NONE、SHORT、MEDIUM、LONG、EXTREME）。
	 * 按数据在存储设备上存在的时间长短排序，SHORT < MEDIUM < LONG < EXTREME。这个字段暗示了数据块
	 * 的更新频率，比如WRITE_LIFE_SHORT就暗示了数据块将很快被更新，更新频繁的数据称为热数据（hot），
	 * 反之为冷数据（cold），f2fs还定义了介于二者之间的warm数据。
	 * 
	 * 引入该字段的目的：
	 * flash设备以page为单位写，以block为单位擦除，一个block含32~256个page，并且由于flash电路特性，
	 * 只能将1写成0，0擦除成1，所以当一个block中非全1时，需擦除后才能写入数据（即“写前擦除特性”）。
	 * 如果一个block中冷热数据混存，热数据更新时，flash FTL需要将block中的有效页拷贝到其他空闲bloc
	 * k中，然后写入数据，原来的block需要擦除后待用。在这过程中引入了写放大WAF（Write Amplification
	 * Factor）、器件寿命磨损两个问题。如果做到冷热数据分离，可减少冷数据的拷贝即擦除，避免上述两个
	 * 问题的负面影响。（mark，flash特性待整理）
	 *
	 * 具体用法：kernel代码中f2fs、nvme用到了这个属性（这两个模块都与flash相关的）。
	 * 1）fcntl通过F_SET_RW_HINT设置inode->i_write_hint，对这个文件的写操作，会将该标记传给
	 * bio->bi_write_hint。（可选，用户主动设置）。
	 * 2）f2fs根据自身文件系统的特点，对自己定义的结构NODE、DATA分成了HOT、WARM、COLD三种类型，举例
	 * 来说COLD_DATA对应WRITE_LIFE_EXTREME，在文件系统层做冷热数据分离。
	 * 3）nvme1.3支持Multi-Stream Write,FTL根据WRITE_LIFE_XX将相同life lime的数据写入相同的block中，
	 * 做到冷热数据分离。*/
	unsigned short		bi_write_hint;

	/* bio的执行结果，BLK_STS_XX（其中XX为OK、NOTSUPP、TIMEOOUT……等多个状态，定义在include/linux/blk_types.h中）*/
	blk_status_t		bi_status;
	/* 一个存储器件逻辑上被划分成多个分区，bi_partno表示分区号 */
	u8			bi_partno;

	/* bio chain特性用到__bi_remaining。何时形成 bio chain？两个场景：
	 * 1）bio拆分时，拆分后的bio形成bio chain（拆分后的多个bio，通过bio->bi_private指向前一个bio，以此类推）。
	 * 该流程见后文“bio的merge、split”。
	 * 2）md raid4、raid5、raid6涉及多条带（multi stripe）io时，每个stripe上的访问对应一个bio，这些bio通过bi->bi_next形成bio
	 * chain。以读分布在2个stripe上的数据为例，bio1、bio2（组成了bio chain）分别读两个stripe上的数据，然后聚合成最终的数据返
	 * 回给用户。该流程见make_request（raid456的回调为raid5_make_request）-->
	 * add_stripe_bio函数。
	 *
	 * __bi_remaining用途：代表bio chain中还有几个bio没有处理完，默认值为1。对某一个bio每split产生一个新的bio，__bi_remaining
	 * 加1。chain类型的bio的回调函数为bio_chain_endio，bio_chain_endio-->bio_endio-->bio_remaining_done将__bi_remaining减1后
	 * 判断__bi_remaining是否为0，不为0说明bio并没有处理完（目前只是完成了chain中一个bio），bio_endio直接返回，只有当
	 * __bi_remaining为0了，bio_endio才会正在地执行。*/
	atomic_t		__bi_remaining;

	/* bi_iter指示bio的处理进度（存储器件端起始sector、还剩多少个字节需要读写；
	 * 内存端当前操作的vector是哪个、当前vector中已经完成了多少个字节）. */
	struct bvec_iter	bi_iter;

	/* bio完成时的回调函数，不同驱动、不同文件系统、不同类型的io的回调处理函数是不一样的.*/
	bio_end_io_t		*bi_end_io;

	/* 各功能模块的私有指针，用于实现特殊功能。用途很多，列举部分：
	 * 1)bio chain用bi_private指向parent bio，将一系列关联的bio组成chain。md、bio的拆分都会形成bio chain。
	 * 2)submit_bio_wait需要等待bio完成，bi_private指向完成量completion
	 * 3)direct io用bi_private将读类型bio组成bio_dirty_list（direct io写类型不需处理）。*/
	void			*bi_private;
#ifdef CONFIG_BLK_CGROUP
	/*
	 * Represents the association of the css and request_queue for the bio.
	 * If a bio goes direct to device, it will not have a blkg as it will
	 * not have a request_queue associated with it.  The reference is put
	 * on release of the bio.
	 */
	struct blkcg_gq		*bi_blkg;
	struct bio_issue	bi_issue;
#ifdef CONFIG_BLK_CGROUP_IOCOST
	u64			bi_iocost_cost;
#endif
#endif

#ifdef CONFIG_BLK_INLINE_ENCRYPTION
	struct bio_crypt_ctx	*bi_crypt_context;
#endif

	union {
#if defined(CONFIG_BLK_DEV_INTEGRITY)
		/* 用于实现end-to-end数据完整性校验功能。T10委员会定义了T10 Protection Information
		 * Model（简称PIM），只规定了host adapter 和storage device之间数据完整性校验规范。
		 * 为了做到end-to-end，bi_integrity中存放校验数据，实现系统调用到I/O controller之间
		 * 数据完整性校验，该机制称作Data Integrity Extensions（简称DIX）。linux用DIX+PIM的
		 * 方式就实现了end-to-end数据校验 */
		struct bio_integrity_payload *bi_integrity; /* data integrity */
#endif
	};

	/* bio中当前vector（简称bvec）数量，不能大于bio->bi_max_vecs。bio->bi_io_vec[bio->bi_vcnt]
	 * 得到的vector是空闲可用的。read、write系统调对应的bio只有一个vector。readv、writev支持scatter-gather
	 * io，会有多个vector。通过bio_add_hw_page、__bio_add_page往bio添加一个内存端属性时，bi_vcnt加1 */
	unsigned short		bi_vcnt;	/* how many bio_vec's */

	/*
	 * Everything starting with bi_max_vecs will be preserved by bio_reset()
	 */

	/* bio中vector最大值，分配bio时设置，见bio_alloc_bioset、bio_init函数 */
	unsigned short		bi_max_vecs;	/* max bvl_vecs we can hold */

	/* bio的引用计数，__bi_cnt大于0，bio_put不会释放bio内存。*/
	atomic_t		__bi_cnt;	/* pin count */

	/* bio中的vector（简称bvec）数量小于等于BIO_INLINE_VECS（值为4）时，bio->bi_io_vec指向bio内嵌的
	 * bio->bi_inline_vecs,否则指向按需分配的vector地址。不管是bio->bi_inline_vecs还是按需分配的vector，
	 * 这些vector在虚拟地址上是连续的，本质上就是一个元素为struct bio_vec的数组，bio->bi_io_vec指向数组
	 * 第一个元素，将地址（bio->bi_io_vec）加1即可得到下一个元素（bvec） */
	struct bio_vec		*bi_io_vec;	/* the actual vec list */

	/* bio结构体在内核中会频繁的申请、释放，为了提升性能、避免内存碎片，内核用slab管理bio内存，slab中存
	 * 放相同大小的object（object就是struct bio），这些objcect就构成了内存池。需要bio时，从内存池申请，
	 * 释放时返回给内存池。bi_pool就指向某个内存池。内核各个模块在使用bio时，会在stuct bio前、后填充一些
	 * 自己的数据，即各个模块需要的bio的大小是不同的，所以我们在代码中会看到fs_bio_set、blkdev_dio_pool、
	 * iomap_ioend_bioset、f2fs_bioset、btrfs_bioset等这些bio内存池。*/
	struct bio_set		*bi_pool;

	/*
	 * We can inline a number of vecs at the end of the bio, to avoid
	 * double allocations for a small number of bio_vecs. This member
	 * MUST obviously be kept at the very end of the bio.
	 */
	/* bio内嵌了BIO_INLINE_VECS（值为4）个vector（struct bio_vec）。若bio需要的vector数量小于等于
	 * BIO_INLINE_VECS，那么直接用这里预定义的bi_inline_vecs，否则按需申请连续的vector */
	struct bio_vec		bi_inline_vecs[];
};

#define BIO_RESET_BYTES		offsetof(struct bio, bi_max_vecs)

/*
 * bio flags
 */
enum {
	BIO_NO_PAGE_REF,	/* don't put release vec pages */
	BIO_CLONED,		/* doesn't own data */
	BIO_BOUNCED,		/* bio is a bounce bio */
	BIO_WORKINGSET,		/* contains userspace workingset pages */
	BIO_QUIET,		/* Make BIO Quiet */
	BIO_CHAIN,		/* chained bio, ->bi_remaining in effect */
	BIO_REFFED,		/* bio has elevated ->bi_cnt */
	BIO_THROTTLED,		/* This bio has already been subjected to
				 * throttling rules. Don't do it again. */
	BIO_TRACE_COMPLETION,	/* bio_endio() should trace the final completion
				 * of this bio. */
	BIO_CGROUP_ACCT,	/* has been accounted to a cgroup */
	BIO_TRACKED,		/* set if bio goes through the rq_qos path */
	BIO_FLAG_LAST
};

/* See BVEC_POOL_OFFSET below before adding new flags */

/*
 * We support 6 different bvec pools, the last one is magic in that it
 * is backed by a mempool.
 */
#define BVEC_POOL_NR		6
#define BVEC_POOL_MAX		(BVEC_POOL_NR - 1)

/*
 * Top 3 bits of bio flags indicate the pool the bvecs came from.  We add
 * 1 to the actual index so that 0 indicates that there are no bvecs to be
 * freed.
 */
#define BVEC_POOL_BITS		(3)
#define BVEC_POOL_OFFSET	(16 - BVEC_POOL_BITS)
#define BVEC_POOL_IDX(bio)	((bio)->bi_flags >> BVEC_POOL_OFFSET)
#if (1<< BVEC_POOL_BITS) < (BVEC_POOL_NR+1)
# error "BVEC_POOL_BITS is too small"
#endif

/*
 * Flags starting here get preserved by bio_reset() - this includes
 * only BVEC_POOL_IDX()
 */
#define BIO_RESET_BITS	BVEC_POOL_OFFSET

typedef __u32 __bitwise blk_mq_req_flags_t;

/*
 * Operations and flags common to the bio and request structures.
 * We use 8 bits for encoding the operation, and the remaining 24 for flags.
 *
 * The least significant bit of the operation number indicates the data
 * transfer direction:
 *
 *   - if the least significant bit is set transfers are TO the device
 *   - if the least significant bit is not set transfers are FROM the device
 *
 * If a operation does not transfer data the least significant bit has no
 * meaning.
 */
#define REQ_OP_BITS	8
#define REQ_OP_MASK	((1 << REQ_OP_BITS) - 1)
#define REQ_FLAG_BITS	24

enum req_opf {
	/* read sectors from the device */
	REQ_OP_READ		= 0,
	/* write sectors to the device */
	REQ_OP_WRITE		= 1,
	/* flush the volatile write cache */
	REQ_OP_FLUSH		= 2,
	/* discard sectors */
	REQ_OP_DISCARD		= 3,
	/* securely erase sectors */
	REQ_OP_SECURE_ERASE	= 5,
	/* write the same sector many times */
	REQ_OP_WRITE_SAME	= 7,
	/* write the zero filled sector many times */
	REQ_OP_WRITE_ZEROES	= 9,
	/* Open a zone */
	REQ_OP_ZONE_OPEN	= 10,
	/* Close a zone */
	REQ_OP_ZONE_CLOSE	= 11,
	/* Transition a zone to full */
	REQ_OP_ZONE_FINISH	= 12,
	/* write data at the current zone write pointer */
	REQ_OP_ZONE_APPEND	= 13,
	/* reset a zone write pointer */
	REQ_OP_ZONE_RESET	= 15,
	/* reset all the zone present on the device */
	REQ_OP_ZONE_RESET_ALL	= 17,

	/* SCSI passthrough using struct scsi_request */
	REQ_OP_SCSI_IN		= 32,
	REQ_OP_SCSI_OUT		= 33,
	/* Driver private requests */
	REQ_OP_DRV_IN		= 34,
	REQ_OP_DRV_OUT		= 35,

	REQ_OP_LAST,
};

enum req_flag_bits {
	__REQ_FAILFAST_DEV =	/* no driver retries of device errors */
		REQ_OP_BITS,
	__REQ_FAILFAST_TRANSPORT, /* no driver retries of transport errors */
	__REQ_FAILFAST_DRIVER,	/* no driver retries of driver errors */
	__REQ_SYNC,		/* request is sync (sync write or read) */
	__REQ_META,		/* metadata io request */
	__REQ_PRIO,		/* boost priority in cfq */
	__REQ_NOMERGE,		/* don't touch this for merging */
	__REQ_IDLE,		/* anticipate more IO after this one */
	__REQ_INTEGRITY,	/* I/O includes block integrity payload */
	__REQ_FUA,		/* forced unit access */
	__REQ_PREFLUSH,		/* request for cache flush */
	__REQ_RAHEAD,		/* read ahead, can fail anytime */
	__REQ_BACKGROUND,	/* background IO */
	__REQ_NOWAIT,           /* Don't wait if request will block */
	/*
	 * When a shared kthread needs to issue a bio for a cgroup, doing
	 * so synchronously can lead to priority inversions as the kthread
	 * can be trapped waiting for that cgroup.  CGROUP_PUNT flag makes
	 * submit_bio() punt the actual issuing to a dedicated per-blkcg
	 * work item to avoid such priority inversions.
	 */
	__REQ_CGROUP_PUNT,

	/* command specific flags for REQ_OP_WRITE_ZEROES: */
	__REQ_NOUNMAP,		/* do not free blocks when zeroing */

	__REQ_HIPRI,

	/* for driver use */
	__REQ_DRV,
	__REQ_SWAP,		/* swapping request. */
	__REQ_NR_BITS,		/* stops here */
};

#define REQ_FAILFAST_DEV	(1ULL << __REQ_FAILFAST_DEV)
#define REQ_FAILFAST_TRANSPORT	(1ULL << __REQ_FAILFAST_TRANSPORT)
#define REQ_FAILFAST_DRIVER	(1ULL << __REQ_FAILFAST_DRIVER)
#define REQ_SYNC		(1ULL << __REQ_SYNC)
#define REQ_META		(1ULL << __REQ_META)
#define REQ_PRIO		(1ULL << __REQ_PRIO)
#define REQ_NOMERGE		(1ULL << __REQ_NOMERGE)
#define REQ_IDLE		(1ULL << __REQ_IDLE)
#define REQ_INTEGRITY		(1ULL << __REQ_INTEGRITY)
#define REQ_FUA			(1ULL << __REQ_FUA)
#define REQ_PREFLUSH		(1ULL << __REQ_PREFLUSH)
#define REQ_RAHEAD		(1ULL << __REQ_RAHEAD)
#define REQ_BACKGROUND		(1ULL << __REQ_BACKGROUND)
#define REQ_NOWAIT		(1ULL << __REQ_NOWAIT)
#define REQ_CGROUP_PUNT		(1ULL << __REQ_CGROUP_PUNT)

#define REQ_NOUNMAP		(1ULL << __REQ_NOUNMAP)
#define REQ_HIPRI		(1ULL << __REQ_HIPRI)

#define REQ_DRV			(1ULL << __REQ_DRV)
#define REQ_SWAP		(1ULL << __REQ_SWAP)

#define REQ_FAILFAST_MASK \
	(REQ_FAILFAST_DEV | REQ_FAILFAST_TRANSPORT | REQ_FAILFAST_DRIVER)

#define REQ_NOMERGE_FLAGS \
	(REQ_NOMERGE | REQ_PREFLUSH | REQ_FUA)

enum stat_group {
	STAT_READ,
	STAT_WRITE,
	STAT_DISCARD,
	STAT_FLUSH,

	NR_STAT_GROUPS
};

#define bio_op(bio) \
	((bio)->bi_opf & REQ_OP_MASK)
#define req_op(req) \
	((req)->cmd_flags & REQ_OP_MASK)

/* obsolete, don't use in new code */
static inline void bio_set_op_attrs(struct bio *bio, unsigned op,
		unsigned op_flags)
{
	bio->bi_opf = op | op_flags;
}

static inline bool op_is_write(unsigned int op)
{
	return (op & 1);
}

/*
 * Check if the bio or request is one that needs special treatment in the
 * flush state machine.
 */
static inline bool op_is_flush(unsigned int op)
{
	return op & (REQ_FUA | REQ_PREFLUSH);
}

/*
 * Reads are always treated as synchronous, as are requests with the FUA or
 * PREFLUSH flag.  Other operations may be marked as synchronous using the
 * REQ_SYNC flag.
 */
static inline bool op_is_sync(unsigned int op)
{
	return (op & REQ_OP_MASK) == REQ_OP_READ ||
		(op & (REQ_SYNC | REQ_FUA | REQ_PREFLUSH));
}

static inline bool op_is_discard(unsigned int op)
{
	return (op & REQ_OP_MASK) == REQ_OP_DISCARD;
}

/*
 * Check if a bio or request operation is a zone management operation, with
 * the exception of REQ_OP_ZONE_RESET_ALL which is treated as a special case
 * due to its different handling in the block layer and device response in
 * case of command failure.
 */
static inline bool op_is_zone_mgmt(enum req_opf op)
{
	switch (op & REQ_OP_MASK) {
	case REQ_OP_ZONE_RESET:
	case REQ_OP_ZONE_OPEN:
	case REQ_OP_ZONE_CLOSE:
	case REQ_OP_ZONE_FINISH:
		return true;
	default:
		return false;
	}
}

static inline int op_stat_group(unsigned int op)
{
	if (op_is_discard(op))
		return STAT_DISCARD;
	return op_is_write(op);
}

typedef unsigned int blk_qc_t;
#define BLK_QC_T_NONE		-1U
#define BLK_QC_T_SHIFT		16
#define BLK_QC_T_INTERNAL	(1U << 31)

static inline bool blk_qc_t_valid(blk_qc_t cookie)
{
	return cookie != BLK_QC_T_NONE;
}

static inline unsigned int blk_qc_t_to_queue_num(blk_qc_t cookie)
{
	return (cookie & ~BLK_QC_T_INTERNAL) >> BLK_QC_T_SHIFT;
}

static inline unsigned int blk_qc_t_to_tag(blk_qc_t cookie)
{
	return cookie & ((1u << BLK_QC_T_SHIFT) - 1);
}

static inline bool blk_qc_t_is_internal(blk_qc_t cookie)
{
	return (cookie & BLK_QC_T_INTERNAL) != 0;
}

struct blk_rq_stat {
	u64 mean;
	u64 min;
	u64 max;
	u32 nr_samples;
	u64 batch;
};

#endif /* __LINUX_BLK_TYPES_H */
