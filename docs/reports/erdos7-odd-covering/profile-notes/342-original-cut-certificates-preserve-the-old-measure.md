[Index](../marked_head_profile.md) · [Original prefix completion](340-whole-cover-completion-constrains-original-prefix-loads.md) · [Complete-star continuation](../problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#complete-star-heads-cannot-be-completed-by-arbitrary-odd-tails)

# Original cut certificates preserve the old measure by conditional weighting

This is an ordinary finite-family result and an actual distinct-odd-modulus
counterexample to an unnormalized certificate budget. It is not a covering
contradiction or a Lean result. The full-cut objects and original labels are
those of340; no original pair `(old cofactor,current exponent)` is merged.

## An exact source-preserving finite kernel

For an old point x, let C_v(x) be the finite set of certificates that cover
the entire current subtree rooted at v. A certificate either stops at v,
choosing ONE original active label there, or expands all p children and
chooses a certificate in each. Thus, with N_v the active-label count,

    W_v=|C_v|=N_v+product_(children w) W_w,

with no continuation term at the maximal actual depth. At the root N=0.
The two alternatives are distinct, and different child certificates have
disjoint literal current nodes, so this counts each original-labelled
cut exactly once. Its positive set is precisely340's F_v.

If W_v>0, the following recursion samples a uniform certificate without
enumerating C_v:

- Each individual active stopping label has probability1/W_v.
- Continue with probability `(product W_w)/W_v`, and independently sample
  a uniform child certificate at each child.

When the product is zero, continuation has probability zero and no child
division is performed. Every continuing certificate has probability
`(product W_w)/W_v * product(1/W_w)=1/W_v`; stopping certificates have
the same probability. This proves uniformity by finite induction.

For an arbitrary finite old measure sigma, attach a failure symbol at
points where W_root=0. Define the joint measure by

    nu(dx,cut)=sigma(dx)/W_root(x), cut in C_root(x), W_root(x)>0,
    nu(dx,failure)=sigma(dx), W_root(x)=0.

Its old marginal is exactly sigma. If a whole cover is assumed and sigma
is supported on genuine old survivors R, then R is contained in F_root
and the failure part is zero. Without that condition, discarding failure
and renormalizing gives sigma conditioned on F_root, not sigma.

In contrast, lifting sigma using unweighted counting of all certificates
and globally normalizing gives the old marginal

    W_root(x)*sigma(dx) / integral W_root d sigma.

That formula is undefined if the denominator is zero and generally changes
the old law. An upper bound for this counting integral is not automatically
an estimate under the original physical or killed law.

Let t_i(x) be the conditional probability that the sampled certificate
uses original label i, with t_i=0 on failure. Then

    0<=t_i<=1_(x in C_i),
    sum_i p^-e_i t_i(x)=1_(x in F_root).

The second identity is the exact Kraft identity of each complete cut,
averaged under the conditional kernel. Consequently

    sigma(F_root)=sum_i p^-e_i integral t_i d sigma
                 <=sum_i p^-e_i sigma(C_i).

This preserves the correct source but recovers only the usual original-
label capacity bound unless additional shared restrictions on the t_i or
the actual old cylinder masses are supplied. The normalization does not
itself supply a stronger global bound. At a FIXED x the finite sparse tree
requires one bottom-up count pass and one top-down sampling pass, without
enumerating cuts. With n original labels, W_v<=2^n, since each certificate
is a distinct subset of those labels; the counts have at most n+1 bits.
Missing children give a zero product and need not be expanded. The global
old-law integration can still require exponentially many old observation
states. No efficient uniform family bound follows from the per-point DP.

## Fixed old cofactors, arbitrarily large full-cut counting mass

Fix a prime p>=7 and a current height H>=1. The old primes are3 and5. Put

    d_j=3^j*5^(p-j), j=0,...,p,
    m=15^p.

All old residues are zero. The d_j form a divisibility antichain and have
one common old period m. Use the complete p-ary comb cut of340. At each
depth e<H, its side leaves have current digits1,...,p-1 on the zero spine;
at depth H it has every digit0,...,p-1.

Assign side digits1,...,p-1 the respective main cofactors

    d_0,d_2,d_3,...,d_(p-1).

At depth H assign digit0 the remaining main cofactor d_p. In addition,
at every depth e<H give the digit1 side leaf a SECOND original label,
with cofactor d_1 and the same current prefix. Every label is the literal
CRT class `(0 mod d_j, digit*p^(e-1) mod p^e)`.

There are exactly pH original labels. Each original pair(d_j,e) occurs
at most once, so all full moduli are distinct and odd. For any fixed j,
its assigned current cylinders are pairwise disjoint. To isolate that old
cofactor, choose old valuations exactly j and p-j, with the top valuation
interpreted as zero in the corresponding finite coordinate. An old
cofactor d_k then divides the old point exactly when k<=j and k>=j.
Thus only d_j is active there. Any point in the selected current cylinder
is private to its original label. The entire family is irredundant.

At each bottom leaf there is only one label. All p bottom labels are
therefore necessary for full fibre coverage. They include d_0=5^p and
d_p=3^p, so they force x=0 modm. Conversely all labels are active on that
old cylinder, and their current comb covers every current point. Hence

    F_root={0 modm}.

Every complete cut must use every literal comb leaf. The only choices
are the two original labels at each of the H-1 duplicated side leaves.
The bottom labels force the same old intersection regardless of these
choices; adding d_1 does not increase its LCM. Therefore

    W_root=2^(H-1)*1_(0 modm),
    Haar_old(F_root)=1/m,
    integral W_root dHaar_old=2^(H-1)/m.

The old period and all old cofactors stay fixed as H grows. Thus neither
the full-cut size nor its depth forces its old intersection modulus to
grow. Even with original-modulus uniqueness and actual irredundancy,
the unmerged sum of complete-certificate intersection masses is unbounded.
This does not use a geometric discount of a deepest sibling.

For p=7,H=29, the203 original labels have

    m=170859375,
    Haar_old(F_root)=1/170859375,
    integral W_root dHaar_old=268435456/170859375>1.

The integer1 escapes every original class, so the family is not a cover.
Merging identical geometric certificate events collapses this example to
one event, but must retain the original label provenance; it does not
make that derived event a fresh distinct-modulus label.

## The counting lift can bias even a source entirely supported on covered fibres

Add one depth-one p-way family with main cofactors15*d_j for
j in{0,2,...,p}. Its old residues are all1 and its current roots are all
distinct. These new moduli differ from every preceding original modulus.
All new old classes are disjoint from the first family: each has positive
3 and5 exponents, and old residue1 conflicts with an original old residue0
in at least one prime. The new family is also irredundant by the shifted
old-valuation construction. Its whole-fibre event is

    J={1 mod15^(p+1)},

and it has exactly one full certificate there. On the common old period
15^(p+1), the previous event I={0 mod15^p} has15 points. There are no
mixed certificates, since no old point activates labels in both groups.
Thus W equals2^(H-1) on I,1 on J, and zero elsewhere.

Take sigma to be uniform on I union J. It is supported on genuine old
survivors (there are no p-free labels) and every point in its support has
a complete cut. Nevertheless the unnormalized counting lift changes

    sigma(I)=15/16
    to 15*2^(H-1)/(15*2^(H-1)+1).

At p=7,H=5 this is15/16 versus240/241. The pointwise1/W kernel preserves
15/16 exactly. The full original family is still a noncover: integer2
misses both groups. Coverage of the chosen supported law is not coverage
of every old survivor.

## Exact scope and the remaining global input

The [standalone checker](../frontier/original_cut_weighting.py) reconstructs
every literal original CRT label and verifies each private integer against
every original class. It checks the full-cut dynamic count on an exact old
prefix partition, rather than enumerating a huge full period. On every old
atom it also checks the normalized conditional kernel and its expected
Kraft identity, retaining the failure branch when no cut exists.

The default checks p=7,H=1,2,3,29 and the two-group variant at H=5. At H=29
there are203 original classes,41209 direct private-point membership checks
and435 old atoms. The two-group case has42 original classes,1764 private
membership checks and1653 old atoms. These finite computations support the
constructions; the formulas above follow for every H by the specified comb
and old-antichain argument.

The helper uses Python3.9+ standard-library exact integers and fractions,
reads no certificate and writes no files. It accepts explicit current
primes and heights and works from external directories:

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/original_cut_weighting.py
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/original_cut_weighting.py --current-prime 11 --heights 1 2 --bias-height 2
```

The whole-cover condition R subset F_root remains unused by these
noncovering examples and fails for them. Therefore they do not exclude
a stronger relation coupling the p-free forbidden family, all old
survivors, and the normalized cut-selection probabilities.

The successful complete-star theorem in problem-details04 supplies an
explicit positive-mass product branch and actual conditional cylinder
caps (US1--US5). It uses original(d,e) uniqueness only after those caps,
in the complete per-cofactor weight budget ofUS6--US7. Full-cut counting
and its source-preserving normalization provide neither those caps nor
a replacement shared source inequality. That is the missing global
input in this route; original labels and counts alone do not supply it.
