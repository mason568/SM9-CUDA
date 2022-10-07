# SM9_FREE

标识密码算法SM9（IBC）实现，包括密钥生成、签名验签、密钥交换和加解密等SM9标准中提到的所有功能。

该实现基于[Miracl密码库](https://github.com/miracl/MIRACL)

采用C语言编写，可支持X86、X86_64、ARM等多平台编译。

# 源码关系
 [Miracl密码库](https://github.com/miracl/MIRACL)比较庞大，因此只截取出其中最核心的部分，包括大整数运算，Fp，Fp^2，Fp^4域计算以及Fp和Fp^2上椭圆曲线基础计算等功能。

依赖的所有[Miracl密码库](https://github.com/miracl/MIRACL)文件在文件夹 [SM9_FREE/miracl](https://github.com/songgeng87/SM9_FREE/tree/master/SM9_FREE/miracl) 内。

在 [Miracl密码库](https://github.com/miracl/MIRACL) 基础之上，实现了满足SM9扩域需求的Fp^12和ate-pairing实现，最后在此之上完成了SM9的密钥生成、签名验签、密钥交换和加解密等功能。
所有和SM9相关的文件都在文件夹 [SM9_FREE/sm9](https://github.com/songgeng87/SM9_FREE/tree/master/SM9_FREE/sm9)内。

[SM9Test.c](https://github.com/songgeng87/SM9_FREE/tree/master/SM9_FREE/SM9Test.c)文件内是简单的测试用例，同时对性能做了简单的统计。

# SM9编译测试
可以直接用XCODE进行编译测试

也可用gcc进行编译

make test

./test

# SM9使用方法
#具体返回错误码等可参考sm9_algorithm.h文件

1. 首先需要初始化参数(使用SM9 第五部分 指定的曲线类型和主密钥初始化系统)：

SM9_Init(0,0,32,NULL,NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL );

2. 如果想要使用签名部分

2.1 需要首先生成签名公私钥对：

SM9_MSK msk = SM9_MSK_New(32, cks);  // 申明一个签名主密钥

SM9_MSPK mspk = SM9_MSPK_New(32);   //申明一个主签名公钥

SM9_GenMSignPubKey(&msk, &mspk);  // 生成主签名公钥

2.2 启动签名验签lib

gg = SM9_Set_Sign(mspk.x1, mspk.x2, mspk.y1, mspk.y2, NULL); // 启动签名lib

第二次启动时候可以使用上述生成的gg

SM9_Set_Sign(NULL, NULL, NULL, NULL, gg);

2.3 针对具体id生成签名私钥

SM9_PK pk = SM9_PK_New(5, id);       // 申明一个签名公钥

SM9_SSK sk = SM9_SSK_New(32);            // 申明一个签名私钥
       
SM9_GenSignSecKey(&sk, &pk, &msk); // 由公钥（id）生成签名私钥

2.4 完成签名

SM9_Sign sign = SM9_Sign_New(32);   // 申明一个签名体

SM9_Signature(msg, 20, rand, &sk, &sign); //签名

2.5 验签部分

单独使用验签，同样需要先初始化参数

SM9_Init(0,0,32,NULL,NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL );

和启动签名验签lib

SM9_Set_Sign(NULL, NULL, NULL, NULL, gg);

随后可以根据用户id完成验签

SM9_Verify(msg, 20, &sign, &pk, NULL);

# 开源协议
本代码遵循BSD开源协议，欢迎大家使用

# 性能
在cpu i7 2.3G, 64位单线程环境下：

    签名10000次大约耗时：120秒
    
    验证10000次大约耗时：372秒
    
    加密10000次大约耗时：130秒
    
    解密10000次大约耗时：214秒
    
    密钥交换20000次大约耗时：833秒
