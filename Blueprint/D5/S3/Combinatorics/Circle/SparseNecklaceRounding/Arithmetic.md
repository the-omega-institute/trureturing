# Sparse cyclic heads and physical chain coordinates

## Abstract

Sparse cyclic heads and physical chain coordinates

**Theorem 1.1 (One cyclic cut, with every physical coordinate).**

Lean statement: `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Arithmetic.native_chain_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Arithmetic.native_chain_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite gap lists l,r and a gap a, assume every entry of (l++[a])++r is at least two. Put bits([])=0 and bits(b::s)=1+2^b bits(s). Let k=sum(l)+a+sum(r), e=bits((l++[a])++r), N=2^k-1, h=bits(r++(l++[a])), h'=bits((a::r)++l), z=bits(r), z'=bits(a::r), n=(N-h')/2 and tau=(z'+1)/2. The conversion of e to a natural number is exact because bits is nonnegative.

Then k>=2, 0<e and 3e<=N. Both h,h' are positive odd integers with 3h<=N and 3h'<=N. The winding satisfies 0<=z<h, 0<z'<=h', z' odd, 2^a h=N+h', z'=2^a z+1 and 2^sum(r) e=h+Nz. Moreover 2n=N-h', 2tau=z'+1, N<=3n, n<=N/2 and 1<=tau<=h'. The chain positive mass P=(2^(a-1)-1)h satisfies P=n+h'-h. Its positive charge plus tau is (2^(a-1)-1)z+tau=z'-z. The direction margin n+h'-e is strictly positive, and 2n+z'<=N. No assumption of distinct heads or minimal period occurs.

The fresh source value actualSource(k+1,2e) at label k is e. For every natural t<=a-2, the original label i=sum(r)+t is less than k. With mass=2^t h and charge=2^t z, it has 0<mass, 3mass<=N and 0<=charge<mass. Its two literal centered values are actualSource(k,e,i)=mass and actualSource(k+1,2e,i)=2mass-charge. At i=sum(r)+a-1 the two centered values are -n and -2n-tau, where 0<n, 0<2n+tau<=N. All labels are indices, even when the resulting values coincide.

The head bound follows by induction on a gap list: 3bits(s)+1<=2^sum(s). In a nonempty induction step the first power is at least four. Applying this inequality to both cyclic cuts gives the uniform bounds. Concatenation gives bits(l++r)=bits(l)+2^sum(l)bits(r), which proves the exact seam and winding equations. Integer parity makes n and tau integral. Centered uniqueness identifies the displayed coordinates with the physical source; the fresh-value result is reused from the existing physical repetition arithmetic. These are local chain coordinates and do not by themselves assert an interleaving theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Arithmetic.native_chain_coordinates`
- Dependency: [D5/S3/Combinatorics/Circle/PhysicalJointRepetition/Repetition](../PhysicalJointRepetition/Repetition.md)
