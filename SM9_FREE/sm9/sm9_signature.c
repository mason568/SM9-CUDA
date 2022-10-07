//
//  sm9_signature.c
//  SM9_FREE
//
//  Created by 宋赓 on 2017/3/25.
//  Copyright © 2017年 宋赓. All rights reserved.
//
#include <stdio.h>
#include "sm9_algorithm.h"
#include "sm9_utils.h"
#include <time.h>
#include <sys/time.h>
#include <stdlib.h>

//test 参数
int showonlyonetimeflag = 1;
int showonlyonetimeflag_verify = 1;

BOOL SM9_GenSignSecKey(SM9_SSK *sk, SM9_PK *pk,SM9_MSK *msk){
    miracl *mr_mip;
    unsigned char *id;
    big ssk,k;
    ecn *ppk;
    if (!sm9sign){
    //    printf("the sm9 sign lib is not init, please run SM9_SET_SIGN function\n");
        return LIB_NOT_INIT;
    }
   
    
    mr_mip = GenMiracl(sk->secLevel);
    id = (unsigned char *)malloc(sizeof(unsigned char)*(pk->keylen+1));
    memcpy(id, pk->pk, pk->keylen);
    memcpy(id+pk->keylen, hid, 1);
    printf("ida+hid,i.e.,ID_[A]||hid:\n");
    print_hex(id,pk->keylen+1);
    k = mirvar(_MIPP_ 0);
    ppk = epoint_init(_MIPPO_);
    
    
    
    ssk = Hfun(_MIPP_ (char *)id,pk->keylen+1,sk->secLevel,1);
    /*  printf begin H_1(ID_[A]||hid,N) */
    printf("在有限域上计算H_1(ID_[A]||hid,N):\n");
    char * tmp_t1 = (unsigned char *)malloc(sizeof(unsigned char)*(sk->secLevel));
    big_to_bytes(_MIPP_ sk->secLevel, ssk, (char *)tmp_t1, TRUE);
    print_hex(tmp_t1,sk->secLevel);
    /*  printf end H_1(ID_[A]||hid,N) */

    bytes_to_big(_MIPP_ msk->keylen, (char *)msk->msk, k);
    add(_MIPP_ ssk, k, ssk);

    /*  printf begin t_1 */
    printf("在有限域上计算t_1,i.e.,t_1=H_1(ID_[A]||hid,N)+ks:\n");
    char * tmp_t2 = (unsigned char *)malloc(sizeof(unsigned char)*(sk->secLevel));
    big_to_bytes(_MIPP_ sk->secLevel, ssk, (char *)tmp_t2, TRUE);
    print_hex(tmp_t2,sk->secLevel);
    /*  printf end t_1 */



    divide(_MIPP_ ssk, sm9n, sm9n);
    
    xgcd(_MIPP_ ssk, sm9n, ssk, ssk, ssk);
    multiply(_MIPP_ ssk,k,ssk);



    divide(_MIPP_ ssk, sm9n, sm9n);
    
    ecurve_mult(_MIPP_ ssk, &p1G1, ppk);
    epoint_norm(_MIPP_ ppk);
    /*  printf begin t_2 */
    printf("在有限域上计算t_2,i.e.,t_2=ks*t_1^{-1}:\n");
    char * tmp_t3 = (unsigned char *)malloc(sizeof(unsigned char)*(sk->secLevel));
    big_to_bytes(_MIPP_ sk->secLevel, ssk, (char *)tmp_t3, TRUE);
    print_hex(tmp_t3,sk->secLevel);
    /*  printf end t_2 */
    epoint_get(_MIPP_ ppk, ssk, k);   // t2*P1 
    big_to_bytes(_MIPP_ sk->secLevel, ssk, (char *)sk->x, TRUE);
    big_to_bytes(_MIPP_ sk->secLevel, k, (char *)sk->y, TRUE);
    
    mirkill(ssk);
    mirkill(k);
    epoint_free(ppk);
    free(id);

    CloseMiracl(_MIPPO_);

    //test free
    free(tmp_t1);
    free(tmp_t2);
    free(tmp_t3);
    return 0;
}

int SM9_Signature(unsigned char* mes,unsigned int meslen,unsigned char* ran,SM9_SSK *sk, SM9_Sign *sign){
    miracl *mr_mip;
	big x,y,r,zero,h;
	zzn12 w;
	ecn *pa;
	int mwlen;
    unsigned char *mw;
	if (!sm9sign){
    //    printf("the sm9 sign lib is not init, please run SM9_SET_SIGN function\n");
        return LIB_NOT_INIT;
    }
    mr_mip = GenMiracl(sm9len);
    x = mirvar(_MIPP_ 0);
    y = mirvar(_MIPP_ 0);
    r = mirvar(_MIPP_ 0);
	h = mirvar(_MIPP_ 0);
	zero = mirvar(_MIPP_ 0);
    
    zzn12_mirvar(_MIPP_ &w);

    
    pa = epoint_init(_MIPPO_);
    
    bytes_to_big(_MIPP_ sk->secLevel, (char *)sk->x, x); //sk->x是私钥ds_A的x分量
    bytes_to_big(_MIPP_ sk->secLevel, (char *)sk->y, y);

    if (!epoint_set(_MIPP_ x, y, 1, pa)){
        zzn12_kill(_MIPP_ &w);
        mirkill(r);
        mirkill(x);
        mirkill(y);
        mirkill(h);
        epoint_free(pa);
        CloseMiracl(_MIPPO_);
        return  NOT_ON_G1;
    }



    zzn12_copy(&gGt, &w);
    /* begin printf 计算群G_T中的元素 g=e(P1,P_{pub-s}) */
    if(showonlyonetimeflag){
        printf("预计算结果,群G_T中的元素 g=e(P1,P_{pub-s}):\n");
        print_zzn12(_MIPP_ &w,sk->secLevel);   //打印一个十二阶扩域w的最后一个分量，长度为len Byte
   
    }
    /* end printf 计算群G_T中的元素 g=e(P1,P_{pub-s}) */

    bytes_to_big(_MIPP_ sk->secLevel, (char *)ran, r);
    zzn12_pow(_MIPP_ &w, r);

    /* begin printf 计算群G_T中的元素 w=g^r */
    if(showonlyonetimeflag){
        printf("计算群G_T中的元素 w=g^r:\n");
        print_zzn12(_MIPP_ &w,sk->secLevel);   
    }
    /* end printf 计算群G_T中的元素 w=g^r */

    mwlen = meslen+sk->secLevel*12;
    mw = (unsigned char *)malloc(sizeof(unsigned char)*(mwlen));

    memcpy(mw, mes, meslen);//把msg拷贝到mw

    zzn12_tochar(_MIPP_ &w, mw+meslen,sm9len);  //M||w然后放到mw的操作实际在这里

    /* begin printf 点w并上需要签名的消息M||w */
    if(showonlyonetimeflag){
        printf("点w并上需要签名的消息M||w:\n");
        print_hex(mw,mwlen);   
    }
    /* end printf 点w并上需要签名的消息M||w */

    h = Hfun(_MIPP_ (char *)mw, mwlen, sk->secLevel, 2);

    /* begin printf 计算 H2的值 h = H_2(M||w,N): */
    if(showonlyonetimeflag){
        printf("计算 H2的值 h = H_2(M||w,N):\n");
        print_big(_MIPP_ h,sk->secLevel);   
   
    }
    /* end printf 计算 H2的值 h = H_2(M||w,N): */

    /* begin printf 随机数r: */
    if(showonlyonetimeflag){
        
        printf("随机数r:\n");
        print_big(_MIPP_ r,sk->secLevel);   
   
    }
    /* end printf 随机数r: */
    subtract(_MIPP_ r, h, r);//计算l=(r-h) 

    divide(_MIPP_ r, sm9n, sm9n);//l = l mod N


    
    
    if (mr_compare(zero, r)==0){
        zzn12_kill(_MIPP_ &w);
        mirkill(r);
        mirkill(x);
        mirkill(y);
        mirkill(h);
        mirkill(zero);
        free(mw);
        epoint_free(pa);
        CloseMiracl(_MIPPO_);
        return  SIGN_ZERO_ERROR;
    }
    /* begin printf 计算l=(r-h) mod N: */
    if(showonlyonetimeflag){
        printf("计算l=(r-h) mod N:\n");
        print_big(_MIPP_ r,sk->secLevel);   
   
    }
    /* end printf 计算l=(r-h) mod N: */
    ecurve_mult(_MIPP_ r, pa, pa);
    epoint_norm(_MIPP_ pa);
    
    epoint_get(_MIPP_ pa, x, y);
    
    big_to_bytes(_MIPP_ sk->secLevel, x, (char *)sign->xs, TRUE);
    big_to_bytes(_MIPP_ sk->secLevel, y, (char *)sign->ys, TRUE);
    big_to_bytes(_MIPP_ sk->secLevel, h, (char *)sign->h, TRUE);

    /* begin printf 消息的签名为(h,S): */
    if(showonlyonetimeflag){
        printf("消息的签名为(h,S):\n");
        print_big(_MIPP_ h,sk->secLevel);  
        print_hex(sign->xs,sk->secLevel);
        print_hex(sign->ys,sk->secLevel);
   
    }
    /* end printf 消息的签名为(h,S): */

    zzn12_kill(_MIPP_ &w);
    mirkill(r);
    mirkill(x);
    mirkill(y);
    mirkill(h);
    mirkill(zero);
    free(mw);
    epoint_free(pa);
    CloseMiracl(_MIPPO_);
    //test ctrl
    showonlyonetimeflag = 0;
    
    return 0;
}

int SM9_Verify(unsigned char *mes,unsigned int meslen, SM9_Sign *sign, SM9_PK *pk, SM9_MSPK *mpk){
    miracl *mr_mip;
	
	
    
    int re;
    
    big h,x,y,h1,h2;
    ecn *S;
    ecn2 pp;
    ecn2 P;
    zzn12 t;
    zzn12 g;
    
    unsigned char *id;

	 int mwlen;
    unsigned char *mw;
    
    if (!sm9sign){
    //    printf("the sm9 sign lib is not init, please run SM9_SET_SIGN function\n");
        return LIB_NOT_INIT;
    }
	mr_mip = GenMiracl(sm9len);
    h = mirvar(_MIPP_ 0);
    x = mirvar(_MIPP_ 0);
    y = mirvar(_MIPP_ 0);
    S = epoint_init(_MIPPO_);
    ecn2_mirvar(_MIPP_ &pp);
    ecn2_mirvar(_MIPP_ &P);
    zzn12_mirvar(_MIPP_ &t);
    zzn12_mirvar(_MIPP_ &g);
    
    bytes_to_big(_MIPP_ sign->secLevel, (char *)sign->h, h);
    
    if((mr_compare(h, sm9n) >= 0) || (mr_compare(h, x)) < 0){
        mirkill(h);
        mirkill(x);
        mirkill(y);
        epoint_free(S);
        zzn12_kill(_MIPP_ &t);
        zzn12_kill(_MIPP_ &g);
        ecn2_kill(_MIPP_ &pp);
        ecn2_kill(_MIPP_ &P);
        return VERIFY_ERROR_1;
    }
    
    bytes_to_big(_MIPP_ sign->secLevel, (char *)sign->xs, x);
    bytes_to_big(_MIPP_ sign->secLevel, (char *)sign->ys, y);
    
    if(!(epoint_set(_MIPP_ x, y, 1, S))){
        mirkill(h);
        mirkill(x);
        mirkill(y);
        epoint_free(S);
        zzn12_kill(_MIPP_ &t);
        zzn12_kill(_MIPP_ &g);
        ecn2_kill(_MIPP_ &pp);
        ecn2_kill(_MIPP_ &P);
        return NOT_ON_G1;
    }
    
    if (mpk == NULL){
        zzn12_copy(&gGt, &g);
        ecn2_copy(&ppG2, &pp);
    }else{
        //todo
        zzn12_copy(&gGt, &g);
        ecn2_copy(&ppG2, &pp);
    }
    ecn2_copy(&p2G2, &P);
    
    /* begin printf 群G_T中的元素 g=e(P1,P_{pub-s}) */
    if(showonlyonetimeflag_verify){
        printf("预计算结果,群G_T中的元素 g=e(P1,P_{pub-s}):\n");
        print_zzn12(_MIPP_ &g,sm9len);  
    }
    /* end printf 计算群G_T中的元素 g=e(P1,P_{pub-s}) */


    /* begin printf 待验证的签名h */
    if(showonlyonetimeflag_verify){
        printf("待验证的签名h:\n");
        print_big(_MIPP_ h,sm9len);   
    }
    /* end printf 待验证的签名h */



    zzn12_pow(_MIPP_ &g, h);
    
    /* begin printf 计算群G_T中的元素 t=g^r */
    if(showonlyonetimeflag_verify){
        printf("计算群G_T中的元素 t=g^r:\n");
        print_zzn12(_MIPP_ &g,sm9len);  
    }
    /* end printf 计算群G_T中的元素 t=g^r */

    id = (unsigned char *)malloc(sizeof(unsigned char)*(pk->keylen+1));
    memcpy(id, pk->pk, pk->keylen);
    memcpy(id+pk->keylen, hid, 1);
    
    
    h1 = Hfun(_MIPP_ (char *)id, pk->keylen+1, sign->secLevel, 1);
    
    /* begin printf 计算 H_1的值 h_1 = H_1(ID_A||hid,N): */
    if(showonlyonetimeflag_verify){
        printf("计算 H2的值 h = H_2(M||w,N):\n");
        print_big(_MIPP_ h1,sm9len);   
   
    }
    /* end printf 计算 H2的值 h = H_2(M||w,N): */
    
    ecn2_mul(_MIPP_ h1, &P); //P=[h_1]P_2
    
    ecn2_add(_MIPP_ &pp, &P); //P=P+pp=P+P_{pub-s}
    
    /* begin printf 计算 群G2中的元素P的值 P=[h_1]P_2 + P_{pub-s}: */
    if(showonlyonetimeflag_verify){
        printf("计算 群G2中的元素P的值 P=[h_1]P_2 + P_{pub-s}:\n");
        print_ecn2(_MIPP_ &P,sm9len);   
   
    }
    /* end printf 计算 群G2中的元素P的值 P=[h_1]P_2 + P_{pub-s} */

    //   ecn2_norm(_MIPP_ &P);
    


    if(!ecap(_MIPP_ &P, S, sm9t, &sm9X, &t)){          //这里是一次双线性对计算 e(S',P)结果存到 t
        mirkill(h);
        mirkill(x);
        mirkill(y);
        epoint_free(S);
        zzn12_kill(_MIPP_ &t);
        zzn12_kill(_MIPP_ &g);
        ecn2_kill(_MIPP_ &pp);
        ecn2_kill(_MIPP_ &P);
        free(id);
        return VERIFY_ERROR_2;
    }
    



    
    /* begin printf 计算群G_T中的元素 u= e(S',P) */
    if(showonlyonetimeflag_verify){
        printf("计算群G_T中的元素 u= e(S',P):\n");
        print_zzn12(_MIPP_ &t,sm9len);   
    }
    /* end printf 计算群G_T中的元素 u= e(S',P)*/

    zzn12_mul(_MIPP_ &t, &g, &t);
    /* begin printf 计算群G_T中的元素 w'= u * t */
    if(showonlyonetimeflag_verify){
        printf("计算群G_T中的元素 w'= u * t:\n");
        print_zzn12(_MIPP_ &t,sm9len);   
    }
    /* end printf 计算群G_T中的元素 w'= u * t*/
    
    
   
    mwlen = meslen+sign->secLevel*12;
    mw = (unsigned char *)malloc(sizeof(unsigned char)*(mwlen));
    memcpy(mw, mes, meslen);
    zzn12_tochar(_MIPP_ &t, mw+meslen,sm9len);
    /* begin printf 消息的并M'||w' */
    if(showonlyonetimeflag_verify){
        printf("消息的并M'||w':\n");
        print_hex(mw,mwlen);   
    }
    /* end printf 消息的并M'||w'*/
    
    h2 = Hfun(_MIPP_ (char *)mw, mwlen, sign->secLevel, 2);
    /* begin printf 自己计算得到的hash值 h_2 : */
    if(showonlyonetimeflag_verify){
        printf("自己计算得到的hash值 h_2:\n");
        print_big(_MIPP_ h2,sm9len);   
   
    }
    /* end printf 自己计算得到的hash值 h_2: */
    re = mr_compare(h2, h);
    if (re!=0) re=VERIFY_ERROR_3;

    /* begin printf 验证通过 : */
    if(showonlyonetimeflag_verify){
        printf("验证通过!\n");
    }
    /* end printf 验证通过 */

    mirkill(h);
    mirkill(h1);
    mirkill(h2);
    mirkill(x);
    mirkill(y);
    epoint_free(S);
    zzn12_kill(_MIPP_ &t);
    zzn12_kill(_MIPP_ &g);
    ecn2_kill(_MIPP_ &pp);
    ecn2_kill(_MIPP_ &P);
    free(id);
    free(mw);
    CloseMiracl(_MIPPO_);

    //test
    showonlyonetimeflag_verify = 0;
    return re;
}
