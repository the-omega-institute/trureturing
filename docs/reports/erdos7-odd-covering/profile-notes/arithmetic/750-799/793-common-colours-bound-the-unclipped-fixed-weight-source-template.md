# Common colours bound the un-clipped fixed-weight source template

Even exact retention of every shared mixed-support colour cannot make the
UN-CLIPPED signed source response of [Report789](789-eight-small-primes-local-ternary-depth-two-and-complete-tail.md)
uniformly exceed

    c_signed=11371478021/781432043175
            =0.014552101005222513... .                 (C1)

This ceiling holds for every globally fixed probability on the five
ternary leaves, including nonsymmetric probabilities. It lies below the
smallest source mass usable by the existing complete-query hinge bound to
certify B<28. Thus merely improving pair-deficit allocation, retaining all
triple consistency, or tuning fixed weights cannot close that particular
uniform signed-response route to29.

This is a limitation of a specified lower-bound template on its completed
budget domain. It is NOT an upper bound on any actual survivor mass. It
does not exclude per-leaf nonnegative clipping, source weights chosen after
the actual star parameters, or estimates retaining additional arithmetic
phase compatibility. In fact the two witnesses explicitly leave the
clipping route open. All results below are ordinary finite arguments and
exact rational evaluations, not new Lean verification or a resolution of
unrestricted Erdős #7.

## 1. Retain every occurrence of the same colour

Use the seven nonternary coordinates

    Q=(5,7,11,13,17,19,23),       b_q=1/(q-2),

and five ternary leaves grouped A={0,1}, B={2,3,4}. A star vertex assigns
each q a root r_q in{A,B} and a leaf t_q in{0,...,4}. Its exact retained
coordinate mass is

    m_ql=1-b_q[1_(l in r_q)+1_(l=t_q)].

The full completed domain also permits convex root and leaf allocations
at every star coordinate, as in Report789. For U subset Q set

    a_Ul=product_(q in U)b_q product_(q outside U)m_ql.

Each mixed support D, |D|>=2, has ONE common root/leaf colour

    c_Dl=1+1_(l in r_D)+1_(l=t_D).                     (C2)

There are120 such supports,546 unordered disjoint pairs, and210 unordered
pairwise-disjoint triples. No four mixed supports are pairwise disjoint.
The unweighted signed response on leaf l is

    R_l=a_empty,l-sum_D a_Dl c_Dl
          +sum_disjoint{D,E} a_(D union E),l c_Dl c_El
          -sum_disjoint{D,E,F} a_(D union E union F),l c_Dl c_El c_Fl. (C3)

For a fixed leaf law w the signed source response is sum_l w_l R_l.
Report789 establishes its lower-bound relation to the actual survivor by
its one-clique Shearer argument and its exact-mass submeasure construction.
That argument is reused here. We evaluate(C3) without taking separate
extrema for different terms. A support uses the identical c_D in its first
term, in all incident pairs, and in all incident triples.

Define the robust template value

    f(w)=inf_(completed star and mixed allocations) sum_l w_l R_l. (C4)

The domain in(C4) is the completed cap domain, not a claim that every point
of that domain is attained by one arithmetic family. A theorem seeking a
uniform lower bound for this entire domain must in particular hold at the
two concrete points below. Their feasibility in this relaxed domain is
all that the template ceiling requires.

## 2. Two complete colour tables give opposing affine witnesses

Take these star roles in increasing q order, with root labels0=A,1=B:

    V_plus =((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1)),
    V_minus=((0,0),(1,2),(1,3),(1,4),(1,3),(1,4),(1,4)).

The [witness data](../../../frontier/cover-geometry/refined-capped-source/coherent_depth2_colour_witnesses.json)
specify all120 mixed colours for each star. A support is its increasing
seven-bit mask; a colour index5r+t means the single role(r,t) in(C2).
Every role is a legal completed allocation vertex. No pair receives a
private replacement of another pair's role.

Exact evaluation of all terms of(C3) gives

    R_plus=(560536/7952175, 272297/2650725,
            -3022312/7952175, 3206/25245, 3206/25245),

    R_minus=(-67244/176715, 972212/7952175,
              188498/2650725, 6403/42525, 1275734/7952175). (C5)

For a symmetric law w=(a,a,b,b,b), b=(1-2a)/3 and0<=a<=1/2,
these two ONE-configuration responses are the affine functions

    L_plus(a)= (1227469/4771305)a-1002532/23856525,
    L_minus(a)=-(4079494/7952175)a+337621/2650725.     (C6)

Since both configurations lie in(C4)'s domain,

    f(w)<=min(L_plus(a),L_minus(a)).                  (C7)

The first line increases and the second decreases. They meet inside the
interval at a=237713/1080931. Their lower envelope is everywhere at most
its value there, which is exactly(C1). This does not claim that either
configuration minimizes(C3), or that(C1) is an attainable robust optimum.
Only the explicit upper comparison is needed.

## 3. The same ceiling applies to all fixed leaf laws

The domain in(C4) is invariant under all S2 x S3 permutations within the
two root groups. Simultaneously permuting every star leaf and every mixed
colour leaf permutes R in the same way; it does not change root membership.
The infimum of affine functions of w is concave, and this group invariance
gives f(gw)=f(w). Therefore averaging w over the twelve group elements yields

    f(w)<=f(wbar),
    wbar=(a,a,b,b,b), a=(w0+w1)/2, b=(w2+w3+w4)/3.    (C8)

Combine(C8) and(C7). This proves(C1) for all globally fixed probabilities.
Equivalently one can use the24 relabeled witness tables directly: an
infimum is at most their individual values and hence at most either
orbit average. The checker recomputes all twelve relabelings of each table.
The averaging here concerns a mathematical template comparison. It is
not replacing an actual family by separately selected phase optima.

## 4. The complete-query hinge requires a larger source lower bound

Retain the conditional weighted-indicator rearrangement of
[Report790](790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md).
For any five-leaf law its root cap r=max(w0+w1,w2+w3+w4) is at least1/2,
and its leaf cap v=max_l w_l is at least1/5. Its ternary query comparator
has survival probabilities

    P(N3>=2)=r, P(N3>=3)=v,
    P(N3>=k)=v/3^(k-3) for k>=3.

The nonternary comparator on q has

    P(Nq>=k)=((q-1)/(q-2))q^(-(k-1)) for k>=2.

Use independent auxiliary variables and N=N3 product_q Nq, exactly as in
that rearrangement bound. Replacing(r,v) by(1/2,1/5) makes this auxiliary
product stochastically smaller. Write H0(t)=E(N-t)_+ for the resulting
lower comparator. These two cap lower bounds need not be jointly attainable
by a leaf law; using the smaller comparator is a conservative necessary
comparison, not a proposed physical law.

With source mass certificate m, the existing query method returns an
upper bound t+H_(r,v)(t)/m. To make this particular bound strictly less
than28 requires

    m>H_(r,v)(t)/(28-t)>=H0(t)/(28-t).               (C9)

The integer-valued N has an exact full mean

    E N=(9/5) product_(q in Q)(q-1)/(q-2).

Its subthreshold atoms determine H0(t) by subtracting from this full mean;
no height tail is discarded. On each unit interval in0<=t<28, H0(t) is
affine and H0(t)/(28-t) is monotone or constant. Thresholds below0 cannot
improve the comparison at0; thresholds at least28 cannot certify an upper
bound below28. Consequently its infimum over admissible real t<28 is the minimum
at the28 integer thresholds0,...,27. Exact comparisons give

    min_t H0(t)/(28-t)=H0(16)/12
                     =0.022526522831384527...>c_signed. (C10)

The [retained result](../../../frontier/cover-geometry/refined-capped-source/coherent_depth2_colour_ceiling.json)
contains every rational threshold ratio. Thus no uniform m justified by
lower-bounding(C3) over the entire completed domain can make this hinge
method prove B<28. A better query estimate or a smaller actual-domain
model could evade the conclusion; they are not excluded by(C10).

## 5. Leafwise nonnegativity is a genuine remaining option

Both rows in(C5) have one negative entry. Actual surviving mass on any leaf
is nonnegative, so the one-clique bound also permits

    mass(actual source)>=sum_l w_l max(R_l,0).        (C11)

At the crossing weight used in(C7), the two explicit(C11) values are
respectively0.0855183537328899... and0.0982346856117873..., both greater
than(C10). Therefore these witnesses do NOT obstruct(C11). Nor do they
supply a uniform lower bound for it.

The operation max(R_l,0) destroys the automatic separate-concavity argument.
Checking only the old star vertices is insufficient. This is the same
quantifier discipline illustrated by
[Report768](768-adaptive-row-laws-do-not-commute-with-phase-convexification.md),
not evidence that a clipped method fails.

A valid possible certificate has an explicit additional obligation: cover
the product of star simplices by specified products of polytopes. On each
cell choose fixed selectors0<=h_l<=1 and fixed legal deficit shares. Then

    mass(actual source)>=sum_l w_l max(R_l,0)
                         >=sum_l w_l h_l R_l.        (C12)

For the last expression use [Report791](791-uniform-shared-deficits-lower-depth-two-tail-cutoff-to1300.md)'s
pair-deficit response with the nonnegative, possibly subprobability weights
w_l h_l. Its cancellation and separate-concavity proof use neither strict
positivity nor normalization of the weights, so they apply on that cell.
A verified lower bound at every product vertex of every cell proves the
same lower bound throughout the covered domain. Different cells may have
different fixed selectors; no concavity of their pointwise maximum is
asserted. The original source and its moment bounds remain the same.
No such complete cell cover crossing(C10) is supplied here.

The explicit ceiling(C1), its all-fixed-weight extension, and the clipping
scope distinction are the results of this comparison. A new all-height
source or an additional common-phase constraint is still needed for the
unrestricted research goal.

## Exact evidence and scope

The [solver-free checker](../../../frontier/cover-geometry/refined-capped-source/coherent_depth2_colour_ceiling.py)
reads only the two literal tables, reevaluates all120 first terms,546 pairs
and210 triples, and verifies their24 coherent relabelings, affine lines,
intersection and full-height hinge comparison. An independent checker
instead recursively enumerates all independent support sets; it obtains
the same counts, responses and ceiling. The witness search is not required
to reproduce any conclusion. The rational result deliberately records the
clipped values to prevent promoting the signed-template limit into a
survivor-mass or clipped-template limit.

This is a repo-derived comparison within the existing source framework;
concavity, symmetry averaging and the query rearrangement are reused
mathematical tools. There is no claim of a new general averaging theorem
or a new external noncoverage range in this report.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/coherent_depth2_colour_ceiling.py
```
