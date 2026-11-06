# Unbounded quotient and residue selectors

## Abstract

Equal second and third maxima: available-grid arithmetic

Put s=b=c, x=2^a, t=2^d, z=2^s. The original hypothesis is precisely 2<=a<d<s, so x>=4, t>=2x and z>=2t. The unchanged seed is A=1+x+xz+xz^2; the other bases are B=1+t+xt+xzt, L=1+z+zt+xzt, and K=1+z+z^2+z^2t. Enlarged positive bases are 2A, SU=2B-1, SV=2L-1-z, and SW=2K-1-z-z^2. The X terminal's enlarged next base remains A.

Selectors are integers n,H,e,p,w with 1<=n<x, 0<=H<J=2^(s-a-1), e in {0,1}, 0<=p<x, w>=0, and 2w+n+1=x. Set h=xH+e. This describes actual bits of the W mask R=z/2-x+1: bit 0 and exponents a through s-2. It also proves w<2^(a-1), so X[w] is an actual stock selection. The middle doubled endpoints are O=2hL+2pB+B-nK and E=2hSV+2pSU+SU-nSW. The arithmetic proves O>=0 and E<=A-1. A separate discrepancy proof gives E>=2O, hence all four middle strip inequalities.

At s=d+1 write r=2^(d-a). For r=2 choose n=x/2+1, H=1,e=1,p=0. For 4<=r<x choose n=x/r+1,H=1,e=0,p=r-1. For r>=x divide r by x+1. If the residue v is below x choose n=1,H=floor(r/(x+1)),e=0,p=v. If v=x and x>=8 choose n=3,H=floor(3r/(x+1)),e=0,p=x-2. For v=x and x=4 use n=3,H=floor(3r/5),e=1,p=1. The script proves the quotient, residue, parity and mask bounds; the first and last special rows include the smallest parameters.

For d+2<=s<=a+d, divide J by x+1. Its residue v cannot vanish: an odd integer x+1>1 cannot divide a power of two. Choose n=1 and H=floor(J/(x+1)); use e=0,p=v when v<x and e=1,p=x-1 when v=x. In both cases (x+1)h+xp=z/2+e. For s>=a+d+1 use T=(K-B)/2 and the paired available grids (xH+e)L+pB. With q=floor(T/(xL)) and r=T mod xL, the three branches r<=(x-1)B, r<=L+(x-1)B, and r>L+(x-1)B choose respectively a ceiling on the first grid, a ceiling on the second grid, or the first point of the next block. The proof explicitly establishes 0<=H<J, both finite digit bounds, and T<=selected<T+B. The last branch proves q+1<J from the upper stock bound. This is a generic integer lemma, not an enumeration or an extra feasibility assumption.

The first and final seam inequalities are obtained by shifts x=4+u,t=2x+v,z=2t+w and nonnegative polynomial coefficients. The paid final-bank identity F=xB-(x-1)L>0 yields the interblock gap (x-1)(L-B)<B. The high-range threshold lies between zero and the actual stock maximum; the strict gap bound supplies O<2B, which, together with the enlarged discrepancy estimate, supplies E<=A-1.

Attribution: the construction and seam estimates are transcribed from the immutable full-face Pro proof, SHA256 843a54eadf758db11ebce774f223c829ca59f3fd15f0865c30eadefbea91f87d. The explicit three-case grid selector is the caller-derived proof, SHA256 a276f6666b2eede7bf3fae6a9921f8252cc56dd6fec351837388d862ebcb3d58. The construction concerns this equal-maximum face; it makes no claim of literature novelty.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
