# A fixed old-slot rectangle controls arbitrary first-11 residues

Under the finite-window assumptions below, the ONE actual PA law has

    R_Q <= 257/51-mu < 257/51,
    mu=672620076855595943409909974611
        /68001662452997808364737107200000>0,

and therefore R_Q<=5.0293244563752335... . Every first-11 residue is arbitrary; neither a common ray nor color reuse is required. No first-11 occurrence is required to be present. This removes the core-ray, forced-empty-label and first-11 presence restrictions of [report553](553-arbitrary-core-colors-and-arbitrary-outside-phases.md). This is an ordinary repository-derived proof with an exact finite optimization, not Lean verification or unrestricted Erdős #7.

## 1. Precise actual-family scope

The family is finite, every full numerical modulus exceeds one and is Q-smooth for Q={5,7,11,13,17,19}, and each full numerical modulus has at most two original occurrences. All residues are fixed globally.

Inside the old box0<=a,b<=4,a+b>0 retain exactly the48 prescribed originals: at p=5,7 and depthi=1,...,4 the two pure residues j*p^(i-1) modulo p^i,j=1,2; at every positive paira,b<=4 the two mixed CRT residues (3*5^(a-1),t*7^(b-1)),t=3,4. Every old original outside this box is arbitrary.

Inside the first-11 box

    0<=a,b<=7, 1<=e<=4, numerical label5^a*7^b*11^e,

provide two POSSIBLE old slots at every one of the64 cofactor pairs. At p=5,7 and positive depthd, slot0 has residue t_p and slot1 has residue t_p when d=1, otherwise t_p+p, where t5=4,t7=5. Depth zero imposes no condition. Slotj uses its specified5-cylinder AND specified7-cylinder.

For each full label and each slot, include either no original or one original with that old projection. Its FULL residue modulo11^e is arbitrary and independent of every other occurrence. There are512 potential slots; any subset may be present. In particular there are no forced empty numerical labels within the first-11 box. The restriction is at most one occurrence per specified old slot, not merely two occurrences whose projections belong to the union of the two slots: placing both occurrences in one distinct slot is outside this scope.

Every first-11 original outside this box, and all later13/17/19 originals, are arbitrary under the general finite two-copy conditions. No old-slot or first-11 ray restriction applies outside the box.

## 2. A uniform local relaxation

First restrict the old source to the prescribed48 classes only; call it lambda0,ref. Its pure masses are x_ref=313/625,y_ref=1601/2401 and its total mass is53759/214375.

At an old point define the potential active count

    M=sum_(j=0,1) N5,j*N7,j,

where Np,j counts the active depthd=0,...,7 cylinders of slotj at primep. This counts all64 potential cofactors, regardless of which originals are actually present. The actual number of active originals at each11-depth is at most M. Therefore the forbidden11-union has Haar mass at most

    M*gamma, gamma=sum_(e=1)^4 11^(-e)=1464/14641.

The actual allowed11-set has mass g>=g_min(M)=max(0,1-M*gamma). ORIGINAL M must be retained: for M>=11 the lower bound is zero, whereas at M=10 it is11^-4.

Relax the requirement that these sets come from the original cylinders or one global family: at each old point allow any measurable11-set of any massg in[g_min,1]. This contains every admitted actual configuration and can only decrease a minimized objective.

For the seven queries put n=1_C5+1_C7+1_C25, u=1_(old5 part of C55), v=1_(old7 part of C77), and

    A=4-(n-1)_+, t=1_(n>=1)+u+v.

Here A is a positive integer at least2 and t is an integer from0 through3. The exact payoff decomposition is

    f=(n-1)_+ +1_(n>=1)*1_C11
                  +u*1_(11 part of C55)+v*1_(11 part of C77)+1_C121.

For any allowed set of massg, each root query has allowed mass at mostmin(g,1/11), and C121 at mostmin(g,1/121). Consequently

    integral(4-f)k dH11
      >= phi_(A,t)(g)
      =min(5/3,1/g)*[A*g-t*min(g,1/11)-min(g,1/121)].       (AR1)

Define phi(0)=0. The bounds on all four queries can be attained simultaneously within the relaxed class: choose their three root queries equal and C121 nested inside that root; fill C121 first, then the rest of the root, then its complement until the allowed set has massg. Haar measure is nonatomic. The SAME global nested queries work for every old point while the relaxed allowed sets vary. Thus AR1 gives the exact relaxed local optimum, without asserting realization by actual depth-budgeted originals.

## 3. Closed scalar minimum

Write a=1/121 and r=1/11. On[0,a], phi has slope(5/3)(A-t-1); on[a,r], slope(5/3)(A-t); on[r,3/5], slope(5/3)A>0. For g>=3/5 it is

    A-(t/11+1/121)/g,

which is strictly increasing. Since A,t are integers, a minimizing mass is

    g*=max(g_min,
           r if t>A,
           a if t=A,
           0 if t<A).                                   (AR2)

Equivalently, evaluate g_min and whichever ofa,r,3/5,1 lie in the allowed interval. The closed formula and this endpoint method agree. No continuous optimizer or truncation in the original11-period is used.

## 4. Exact finite query certificate

The literal old conditions and all possible slot prefixes give73 leaves at5 and91 at7. Aggregation by(x mod25,y mod7,M) gives209 groups, with uncapped M ranging from2 to68. Every weight is its exact old-survivor Haar mass.

Once the local relaxation is made, the remaining query choices are only

    (a5,a7,a25,a55_old5,a77_old7),

with5*7*25*5*7=30625 tuples. For each tuple, integrate the local AR2 value over the209 groups. Exact integer evaluation gives

    I_min=1262238451165943772442/1661652350530156359375.

One minimizing tuple is(4,6,14,4,6); there are three minimizing tuples. This is a minimum in the allowed-set relaxation, not a claimed actual original-family example.

Set

    F11(x,y)=x/42+y/20+59/840,
    C(x,y)=5xy/363+10x/231+83y/825+4/165,
    G(x,y)=F11(x,y)/3+C(x,y)/4.

Use the actual capped PA kernels of [report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) and the phase-uniform seven-label caps of [report551](551-seven-shallow-labels-control-every-rainbow-continuation.md). For the ACTUAL first-11 kernel, let S11 be its PA mass saving and Dseven=C-sup_queries integral f dlambda11 its joint seven-label deficit. Directly from the definitions,

    S11+Dseven/4
      =G(x,y)-lambda0(1)
          +(1/4)*inf_queries integral(4-f) dlambda11.       (AR3)

Thus at the reference old source, uniformly over every subset of potential first-11 occurrences and every choice of their full11-residues,

    S11+Dseven/4>=kappa_ref
      =280697245759512082027/39879656412723752625000.        (AR4)

## 5. Arbitrary additions outside the two finite windows

The actual raw old-source restriction satisfies lambda0<=lambda0,ref, and its actual pure masses lie in[1/2,313/625] and[2/3,1601/2401]. For any fixed actual finite-core kernel, rewrite the query score in AR3 as

    G(x,y)-integral[1-s+(1/4)*integral(fk)dH11] dlambda0.

The bracket is nonnegative, since s<=1 and f>=0. Therefore shrinking the old source decreases this subtracted charge. All nonconstant coefficients of G are positive, so arbitrary extra old originals cost only

    G_ref-G_min=10687/466908750.                           (AR5)

Now add arbitrary outside-window first-11 originals under this SAME actual lambda0. In one fibre let A' subset A be the new and old allowed sets, delta=H(A\A'), and let h,h' be their capped densities. At zero allowed mass use density5/3; its kernel is zero almost everywhere. The removed kernel mass is h*delta, while its gained mass p=(h'-h)H(A') is at most h*delta. Since -2<=4-f<=4,

    (1/4)*integral(4-f)(k_A'-k_A)
      >=-h*delta-p/2>=-(3/2)h*delta>=-(5/2)delta.           (AR6)

This jointly pays changed first-11 mass and changed seven-label response. There is no second payment for the same change.

Under the actual pure-source domination, define A0=x+1/4,B0=y+1/6 and a_hi=1/(4*5^7),b_hi=1/(6*7^7). The outside labels split disjointly into e>=5 with all old cofactors, and e=1,...,4 with a>=8 or b>=8. The complete two-slot deletion bound is

    J_actual<=2*[A0*B0/(10*11^4)
           +(a_hi*B0+A0*b_hi-a_hi*b_hi)*(1-11^-4)/10]
       <=J_max=149819363/16442035995000.                   (AR7)

The subtraction counts the intersection of numerical exponent ranges; no probability lower bound is subtracted. Unit old cofactors, both numerical slots and all heights are included. The second inequality uses the reference upper pure masses.

Combining AR4--AR7 gives

    S11+Dseven/4>=kappa_final
      =557751981854850601729/79759312825447505250000.        (AR8)

## 6. Complete actual-law consumer

Every actual first-11 kernel still has density at most5/3 and fibre mass at most one. The unconditional complete-query caps and seven-label stability identity therefore give S13>=Dseven/4 via CP5, whether or not Dseven itself is positive. Hence S11+S13>=kappa_final.

All later PA row savings are nonnegative. Actual pure deficits are nonnegative, and the complete actual mixed old union within the pure survivors has mass at most1/12 by the numerical two-copy geometric sum. NC4, with T=257/51 and c0=6168733163201163811/542935350932041267200, yields

    (T-2)*kappa_final-c0
      =672620076855595943409909974611
         /68001662452997808364737107200000 >0.

The actual final PA subprobability has positive mass at most one. Normalize this one law once to obtain the stated R_Q bound, uniformly over all finite queries and hence the complete query norm. No original phase, actual kernel or numerator/denominator source is replaced.

## Verification and boundary

The [standalone producer](../../frontier/cover-geometry/first11_arbitrary_phase_rectangle_bound.py)
and [exact data](../../frontier/cover-geometry/first11_arbitrary_phase_rectangle_bound.json)
construct the old-source partition and all209 groups. The producer
validates AR2 against the endpoint method for all1536 combinations
M=1,...,128, A=2,3,4 and t=0,...,3, and evaluates all30625 old-query
tuples. It also reconstructs the complete geometric PA/NC4 consumer,
checks the outside cap sum in two ways, and tests2184 rational nested
kernel variations in addition to the general proof AR6.
All30 named checks pass. The retained JSON SHA256 is
`7b27d826bde44737af2f630e1e7b557d0ab4679cd7b6244fff43de85bb3a4252`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/first11_arbitrary_phase_rectangle_bound.py
```

Requirements are Python3.10+ and a C++17 compiler with signed128-bit
integers, such as GCC or Clang. Generated source and binaries are
removed with the temporary build directory. The --output and --compiler
options are explicit; the default output is beside the script.
Execution from a different working directory through a script path
containing spaces, without loading shell startup files, produces exactly
the same JSON bytes on the tested macOS host. Other operating systems
were not tested.

An independently written implementation reproduces the209 groups,
uncapped maximum68, the30625-query minimum, all1104 integer lookup
entries and all209 minimizing mass choices. It also independently
checks1536 closed scalar minima and the final constants. The expected
minimum was disclosed before that implementation was run; this is
source-independent verification, not an outcome-blind test. No Lean
build or full original-period enumeration was run.

The fixed old48-class window and the per-slot old projections within the first-11 rectangle remain substantive assumptions. An arbitrary pair of old projections per numerical label is not covered. The allowed-set relaxation is used only for a uniform bound; no minimizing relaxed set is asserted to be generated by an actual original family. This result does not settle arbitrary first-11 geometry, arbitrary two-copy closure or Erdős #7.
