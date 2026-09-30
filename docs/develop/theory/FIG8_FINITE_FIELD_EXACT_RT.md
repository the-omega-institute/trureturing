# Exact all-region RT on a planar figure-eight over odd finite fields

## Theorem (explicit symmetric linear-support family)
Let K be a finite field of odd order q. The planar graph has vertices O,A,B,C,D, edges OA,OB,AB,OC,OD,CD, and two boundary legs at each outer vertex. For nonzero t,s in K define the normalized state

    |Psi(t,s)> = q^(-2) sum_(x,y,z,w in K)
      |x+z,x-z,y+tz,y-tz,x+y+w,x+y-w,x-y+sw,x-y-sw>.

All coefficients here are positive and identical; arbitrary phases are NOT covered.

This state is realized by five normalized AME(4,q) tensors. It satisfies S(R)=m(R) log q for every subset of the eight individual boundary legs if and only if

    t,s not in {0,1,-1},
    st+s+t-1 != 0, st+s-t+1 != 0,
    st-s+t+1 != 0, st-s-t-1 != 0.                 (1)

The initial t,s !=0 is necessary for the stipulated local AME realization. The remaining conditions characterize exact RT within this family, not among all possible tensors.

There are exactly

    (q-3)(q-7) + 4, if q == 1 mod 4;
    (q-3)(q-7),     if q == 3 mod 4

ordered parameter pairs satisfying (1). Consequently this family works over every odd finite field of order at least 9, and over no smaller odd finite field. This is not a minimum-dimension theorem for arbitrary AME networks.

For q=9, take K=F3[i]/(i^2+1), t=i and s=1+i. For any prime characteristic p>=11, t=s=2 works over every finite extension of Fp.

## Local AME realization and normalization
Order the central legs toward A,B,C,D and use

    T_O = q^(-1) sum_(x,y) |x,y,x+y,x-y>.

At each outer vertex order the legs (central,loop,boundary1,boundary2). Use

    T_a = q^(-1) sum_(u,v) |u,v,u+a v,u-a v>,

with a=1,t,1,s at A,B,C,D, respectively. Contract paired internal indices using Kronecker deltas in their displayed bases. No change of coordinates around a loop is assumed. Every pair of the four linear forms u,v,u+av,u-av is independent because a!=0 and 2!=0. Any two labels therefore uniquely determine u,v, proving each normalized local tensor is AME(4,q).

A consistent internal assignment is uniquely specified by x,y,z,w, where z and w are the actual AB and CD edge coordinates. Each boundary support tuple is distinct: the first pair determines x,z, the second determines y, and the third determines w. Every amplitude before normalization is q^(-5). Its norm is q^(-3), giving the displayed normalized amplitude q^(-2). Choosing normalized maximally entangled edge contractions only changes the common scalar before normalization.

## Uniform linear-support entropy lemma
If L is a d-dimensional linear subspace of K^A direct-sum K^B and the state is the positive uniform superposition on L, write a=dim pi_A L and b=dim pi_B L. Define U_A={a:(a,0) in L}, U_B={b:(0,b) in L}; their dimensions are d-b and d-a. The relation L pairs the cosets of U_A in pi_A L bijectively with the cosets of U_B in pi_B L. Each matched pair contributes a complete rectangle of coefficients, a rank-one block. There are q^(a+b-d) disjoint equal-size rectangles, hence precisely q^(a+b-d) equal Schmidt coefficients. Thus

    S(A) = (a+b-d) log q.

This proof uses identical coefficients, not merely equal absolute values. Here d=4 and a,b are the row ranks of the selected and complementary output matrices.

## Analytic min-cut profile
Let k=|R|<=4. For an arbitrary vertex-side assignment let S be the outer vertices on the R side, n=|S|, r the number of selected boundary legs incident to S, and h the number of cut internal edges. The total cut cost is

    k + 2n - 2r + h.

After minimizing the central vertex side, the minimum possible h at a fixed S is 0,2,2 or 4,2,0 for n=0,1,2,3,4 respectively. At n=2 the value 2 occurs exactly for S={A,B} or {C,D}; otherwise it is 4. These follow directly by counting the six displayed internal edges.

Using r<=min(k,2n), every cost is at least k for k<=3. For k=4 this remains true except when S is one complete loop pair and R consists of precisely that pair's four legs; then cost 2 is achievable and is minimal. Placing every graph vertex on the complement side always gives cost k. By complement symmetry:

    m(R) = min(|R|,8-|R|),

except for the two four-leg full-loop regions AB and CD, for which m(R)=2.

## Rank certificate, reduced to four-by-four minors
The eight-by-four output matrix is

    [1  0  1  0]
    [1  0 -1  0]
    [0  1  t  0]
    [0  1 -t  0]
    [1  1  0  1]
    [1  1  0 -1]
    [1 -1  0  s]
    [1 -1  0 -s].

The two full-loop four-row submatrices AB and CD have rank exactly 3 for every nonzero t,s. Their nullspaces are respectively the w-axis and the z-axis. All other four-row minors are nonzero exactly under (1). Here is a compact determinant classification; row permutations and the signs of chosen legs change overall signs:

* Pair occupancy (2,2,0,0): six minors. AB and CD vanish. AC,AD,BC,BD have determinants of absolute algebraic forms 4,4s,4t,4st.
* Pair occupancy (2,1,1,0): 48 minors. After removal of nonzero factors that are signed powers of 2 and monomials in t,s, the only potentially vanishing factors are t-1,t+1,s-1,s+1. Each occurs. The other minors reduce to 1.
* Pair occupancy (1,1,1,1): 16 minors. Up to overall sign these are the four bilinear expressions in (1), each appearing four times.

This is a symbolic determinant identity over Z[t,s], so applies without exceptions to every odd characteristic, including 3 and 5. A complete independent executable certificate accompanies this proof and compares actual finite-field row ranks with direct graph cuts for every subset.

Every <=3 row subset extends to a nonspecial four-row subset, so has full row rank under (1). Every >=5 row subset contains a nonspecial four-row subset, so has rank 4. For a nonspecial four-leg bipartition both ranks are 4, giving entropy 4 log q; for AB|CD both are 3, giving entropy 2 log q. The entropy lemma now gives the complete min-cut profile.

Conversely, exact RT for every nonspecial four-leg region requires rank(F)+rank(G)-4=4. Both ranks are at most 4, so every nonspecial four-row minor must be nonzero, proving necessity of (1).

## Counting and existence
For t not in {0,+1,-1}, the four bilinear exclusions are precisely

    s not in {+a,-a,+a^(-1),-a^(-1)}, a=(t-1)/(t+1).

None is 0 or +/-1. Normally the four values are distinct. They coincide in opposite pairs exactly when a^2=-1, equivalently t^2=-1, in which case there are only two exclusions. (The alternative a^2=1 would imply t=0 or characteristic 2 and is already excluded.) There are q-3 choices of t; each normally leaves q-7 choices of s, and each of the two square roots of -1, when they exist, adds two choices. This proves the count formula and the existence assertion. Over F9 the four bilinear values at (i,1+i) are -1,1+i,i-1,-i, all nonzero.

## Scope and provenance
The graph is planar. The result is a finite tensor-network entropy theorem, not a claim about gravitational RT. Large-dimension existence of simultaneous exact RT with perfect stabilizer tensors is already implied by known random-stabilizer results (literature audit separately). The contribution claimed here is only the explicit small-field positive-support family, sharp parameter criterion and count, and the direct elementary certificate. Novelty against all existing literature has not been established.
