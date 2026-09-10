#include <metal_stdlib>
using namespace metal;

// uint is Metal's unsigned 32-bit integer. Every stored limb is <=255;
// carry <=18, so limb*prime+carry <=255*19+18=4863 (no uint wrap).
// All production factors total <=102, hence value<=19^102<2^510<256^64.
// Synthetic probes also exercise the explicit overflow path at 256^64.
struct Big { uint limb[64]; uint used; uint error; };

Big small(uint v) {
    Big a;
    for (uint k=0;k<64;k++) a.limb[k]=0;
    a.used=1; a.error=0;
    a.limb[0]=v&255;
    while (v>>8) { v>>=8; a.limb[a.used++]=v&255; }
    return a;
}

void mul_prime(thread Big& a, uint p) {
    if (p<1 || p>19) { a.error=1; return; }
    uint carry=0;
    for (uint k=0;k<a.used;k++) {
        uint v=a.limb[k]*p+carry;
        a.limb[k]=v&255; carry=v>>8;
    }
    if (carry) {
        if (a.used==64) a.error=1;
        else a.limb[a.used++]=carry;
    }
}

Big product(uint3 p, uint3 exponents) {
    Big a=small(1);
    for (uint i=0;i<3;i++)
        for (uint e=0;e<exponents[i];e++) mul_prime(a,p[i]);
    return a;
}

int compare(thread const Big& a, thread const Big& b) {
    for (int k=63;k>=0;k--)
        if (a.limb[k]!=b.limb[k]) return a.limb[k]<b.limb[k] ? -1:1;
    return 0;
}

// The first comparison needs X, whereas the second needs X^2. Keep both exact.
uint reflected_guards(thread const Big& R, thread const Big& cube, thread const Big& X,
                      thread const Big& Xsquare, thread const Big& E,
                      thread const Big& middle, thread const Big& upper) {
    Big cutoff=small(5040);
    return uint(compare(R,cutoff)>0) | (uint(compare(cube,X)<0)<<1)
        | (uint(compare(Xsquare,E)<0)<<2) | (uint(compare(middle,E)<0)<<3)
        | (uint(compare(E,upper)<0)<<4);
}

uint3 mask_bits(uint m) { return uint3(m&1,(m>>1)&1,(m>>2)&1); }

void decode(uint id, thread uint& box, thread uint& slot, thread uint& t, thread uint3& b) {
    box=id/25; slot=id%25; t=box/4096;
    uint rem=box%4096; b=uint3(rem/256,(rem/16)%16,rem%16);
}

float exp_term(float x, thread uint& flags) {
    // Conservative flag for possible subnormal/flush-to-zero; never a certificate.
    if (x < -87.0f) flags|=4;
    float v=exp(x);
    if (v==0.0f) flags|=4;
    if (!isfinite(v)) flags|=2;
    return v;
}

constant uint3 orders[6] = {uint3(0,1,2),uint3(0,2,1),uint3(1,0,2),
                            uint3(1,2,0),uint3(2,0,1),uint3(2,1,0)};

void propose(float3 c, float3 d, float3 h, float M0, float M1,
             device float* out, thread uint& flags) {
    float a=M0/3.0f, mu=M1/3.0f, ell=min(c[0],min(c[1],c[2]));
    float3 delta;
    for (uint k=0;k<3;k++) {
        float dc=max(0.0f,max(a-c[k],c[k]-mu));
        float dd=max(0.0f,max(a-d[k],d[k]-mu));
        delta[k]=min(dc,dd);
    }
    float V=dot(delta,delta), rho=sqrt(V/6.0f), L=mu-rho, H=mu+2.0f*rho;
    if (!(L>0.0f) || !isfinite(L) || !isfinite(H)) flags|=2;
    out[0]=M0; out[1]=M1; out[2]=ell; out[3]=L; out[4]=H; out[5]=V;
    float maximum=-INFINITY;
    for (uint order=0;order<6;order++) {
        float remaining=M1-(c[0]+c[1]+c[2]); float3 y;
        for (uint l=0;l<3;l++) {
            uint k=orders[order][l];
            y[k]=clamp(remaining/h[k],0.0f,1.0f); remaining-=h[k];
        }
        float value=0.0f;
        for (uint n=1;n<=24;n++) {
            float nf=float(n);
            float term=exp_term(ell-nf*H,flags)+2.0f*exp_term(ell-nf*L,flags);
            for (uint k=0;k<3;k++) {
                term-=(1.0f-y[k])*exp_term(ell-nf*c[k],flags);
                term-=y[k]*exp_term(ell-nf*d[k],flags);
            }
            value+=term/nf;
        }
        out[8+order]=value; maximum=max(maximum,value);
    }
    out[6]=maximum;
    out[7]=6.0f*exp_term(-24.0f*ell,flags)/(25.0f*(1.0f-exp(-ell)));
    for (uint k=0;k<14;k++) if (!isfinite(out[k])) flags|=2;
}

kernel void search(device int* integers, device float* floats,
                   constant uint* table, constant uint* config,
                   uint tid [[thread_position_in_grid]]) {
    if (tid>=config[1]) return;
    uint id=config[0]+tid, box,slot,t; uint3 b;
    decode(id,box,slot,t,b);
    uint3 p=uint3(table[11*t],table[11*t+1],table[11*t+2]);
    bool adjacent=slot<7;
    uint j=adjacent ? slot+1 : 1+(slot-7)/3;
    int i=adjacent ? -1 : int((slot-7)%3);
    uint lower=table[11*t+3+j-1], upper=table[11*t+3+j];
    int next=adjacent ? -1 : int(table[11*t+3+j+1]);
    device int* out=integers+18*tid;
    out[0]=id; out[1]=box; out[2]=slot; out[3]=t;
    for (uint k=0;k<3;k++) { out[4+k]=b[k]; out[7+k]=p[k]; }
    out[10]=lower; out[11]=upper; out[12]=next; out[13]=j; out[14]=i;
    Big R=product(p,b+mask_bits(lower)), cutoff=small(5040);
    uint bits=uint(compare(R,cutoff)>0), flags=R.error;
    if (!adjacent) {
        uint3 v=b+1+mask_bits(lower), ex=uint3(0), ec=uint3(0);
        ex[i]=3*(2*b[i]+3); ec[i]=3*(b[i]+1);
        Big X=product(p,v), Xsquare=product(p,2*v), E=product(p,ex), cube=product(p,ec);
        Big middle=product(p,2*b+2+mask_bits(lower)+mask_bits(upper));
        Big top=product(p,2*b+2+mask_bits(lower)+mask_bits(uint(next)));
        bits=reflected_guards(R,cube,X,Xsquare,E,middle,top);
        flags|=X.error|Xsquare.error|E.error|cube.error|middle.error|top.error;
    }
    bool active=bits==(adjacent ? 1u:31u);
    out[15]=bits; out[16]=active;
    device float* fp=floats+14*tid;
    for (uint k=0;k<14;k++) fp[k]=NAN;
    if (active) {
        float3 h=log(float3(p)), c=float3(b+1)*h, d=float3(b+2)*h;
        float M0=dot(float3(b+1+mask_bits(lower)),h);
        float M1=adjacent ? dot(float3(b+1+mask_bits(upper)),h) : 3.0f*(c[i]+d[i])-M0;
        propose(c,d,h,M0,M1,fp,flags);
    }
    out[17]=flags;
}

Big read_big(device const int* data) {
    Big a=small(0); a.used=64;
    for (uint k=0;k<64;k++) { a.limb[k]=uint(data[k]); if(a.limb[k]>255) a.error=1; }
    while (a.used>1 && a.limb[a.used-1]==0) a.used--;
    return a;
}

kernel void limb_probe(device int* out, device const int* inputs, device const int* targets,
                       uint tid [[thread_position_in_grid]]) {
    Big a=read_big(inputs+66*tid), b=read_big(targets+64*tid);
    uint p=uint(inputs[66*tid+64]), count=uint(inputs[66*tid+65]);
    for (uint n=0;n<count;n++) mul_prime(a,p);
    for (uint k=0;k<64;k++) out[66*tid+k]=int(a.limb[k]);
    out[66*tid+64]=a.error; out[66*tid+65]=compare(a,b);
}

kernel void guard_probe(device int* out, device const int* inputs,
                        uint tid [[thread_position_in_grid]]) {
    device const int* v=inputs+7*64*tid;
    Big R=read_big(v), cube=read_big(v+64), X=read_big(v+128), Xsq=read_big(v+192);
    Big E=read_big(v+256), middle=read_big(v+320), top=read_big(v+384);
    out[tid]=reflected_guards(R,cube,X,Xsq,E,middle,top);
}

kernel void decode_probe(device int* out, device const int* ids,
                         uint tid [[thread_position_in_grid]]) {
    uint box,slot,t; uint3 b; decode(uint(ids[tid]),box,slot,t,b);
    out[7*tid]=ids[tid]; out[7*tid+1]=box; out[7*tid+2]=slot; out[7*tid+3]=t;
    for (uint k=0;k<3;k++) out[7*tid+4+k]=b[k];
}

kernel void numerical_probe(device float* out, device int* errors, device const float* in,
                            uint tid [[thread_position_in_grid]]) {
    device const float* v=in+8*tid;
    float3 c=float3(v[0],v[1],v[2]), d=float3(v[3],v[4],v[5]);
    uint flags=0; propose(c,d,d-c,v[6],v[7],out+14*tid,flags); errors[tid]=flags;
}
