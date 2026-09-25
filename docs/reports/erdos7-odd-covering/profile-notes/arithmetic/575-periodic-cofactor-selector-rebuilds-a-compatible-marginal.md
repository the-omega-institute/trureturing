# A periodic selector converts cofactor geometry into a good fixed-u law

## Result and its exact scope

Let P={3,5,7,11,13,17,19}, Q=P minus3. Fix distinct p,q in Q and a
nonunit Q-smooth D coprime to pq. Choose three fixed integers r0,r1,r2
whose residues modulo D are pairwise distinct. For an arbitrary N>=0,
put

    d_i=D p^i q^(N-i), 0<=i<=N.

Consider a finite actual original family with distinct nonunit odd
P-smooth full numerical moduli and globally fixed original residues.
Allow arbitrary pure3 originals and arbitrary Q-only originals. Every
remaining mixed original has modulus3^e d_i for some e>=1 and i.
At each d_i impose these two restrictions:

* All actual projections at e=0,1,2,3, if any, have at most ONE distinct
  Q phase a_i. Include any Q-only original at d_i in this statement.
* At every e>=4, the actual Q phase is one of the three GLOBAL phases
  r0,r1,r2 modulo d_i. The chosen phase may vary with i and e. Every
  actual ternary phase and every finite height are arbitrary.

Then there is a fixed-u product/deletion law on the actual survivor,
where u is normalized Haar on the complete actual pure3 survivor, with

    R_P<=6199418183523781383463/539719033471556471250
       =11.486380503663476... <566/49.

It also has Report572's actual23/29 extension and Haar lower bound
>1/37000. This theorem does NOT assume a lower bound on the original
fibres or a pointwise residual-incidence bound before the selector is
constructed. Such fibres may be dead under a different actual PA law.
The result is a sufficient structural class, not an unrestricted result
or a claim of bare noncoverage novelty.

The new mathematical step is the explicit interval selector below.
The PA supplier and ensuing fixed-u lifting estimate are reused from
Reports569 and572; no new general kernel theorem is asserted.

## The selector and its interval proof

At d_i select the at-most-two phases

    A_(d_i)={a_i if it exists} union {r_(i mod3)}.

At every other actual Q-only label select its actual phase. Auxiliary
phases and any missing path label may be added to the selected Q input;
this input is used to choose a supported law, and does not modify the
actual covering family or reselect its original phases. Different d_i
are distinct. Thus each numerical Q modulus still occurs at most twice.
Report569 supplies ONE PA probability nu on the resulting selected
Q survivor V, with R_Q(nu)<=B* and its stated density bound.

Fix one SAME x in V. If x matches a tail phase r_c at any d_i, then
x=r_c modD. Since the three r_c are distinct modD, x cannot match any
other tail color. For that color, the complete set of matching indices
is

    I_c(x)={i:0<=i<=N, i<=v_p(x-r_c), N-i<=v_q(x-r_c)}.

This is an interval of consecutive integers (possibly empty), with
valuation infinity interpreted by truncation at N. The assertion is
just divisibility by D, p^i and q^(N-i), with all other Q coordinates
unchanged.

If I_c(x) contained three or more indices, one would have i=c mod3.
But that phase was selected at d_i, contradicting x in V. Consequently
|I_c(x)|<=2. Actual tail events form a subset of these potential matches,
so at each x in V at most two distinct NUMERICAL cofactors are active.
This proves the required incidence bound from the exponent geometry
and one globally fixed selector; it is not an incidence assumption.

The selected shallow phases remove all e<=3 originals. Numerical
uniqueness and u<=2H3 bound all e>=4 cylinders of one active cofactor
by2 sum_(e>=4)3^-e=1/27. Hence the actual fibre survival satisfies
c(x)>=25/27 on the NEW selected V. Report572 FS2 then constructs the
one marginal-preserving lift of this new nu, and its complete query
bound is B*+(27/25)(1+B*). The raw product prior is w proportional to
nu/c, not the previously supplied marginal. Every query depth and the
same actual survivor mask remain in that application.

The marginal change has no additional scalar query penalty: the
selected input itself meets Report569's two-copy contract, so its new
law is rebuilt with the same uniform B*. This is different from
normalizing a restriction of an arbitrary old nu and bounding its norm
by R(nu)/(1-epsilon).

## An actual irredundant family with a dead fibre under the old PA law

Take p=5,q=7,D=11,N=80, with r0=0,r1=1,r2=2. There are81 cofactors

    d_i=11*5^i*7^(80-i), 0<=i<=80.

For EVERY i include exactly four actual originals, specified in CRT:

|e|Q phase modulo d_i|ternary phase modulo3^e|
|---|---|---|
|0|3|vacuous|
|4|1|i|
|5|2|0|
|6|0|0|

There are324 distinct actual full moduli. No pure3 original is present,
so u=H3. Every d_i has four different actual projected phases; the
original full projection family is not a two-copy input.

Start with the mandatory shallow selector A_i={3}. This is an actual
Report569 PA input. Coordinates5 and7 are Haar. At coordinate11, the
forbidden set is either empty or just root3, so its actual normalized
row has density at most11/10, below the cap5/3. Later coordinates are
Haar. Hence this ONE supplied PA probability nu0 satisfies

    R_Q(nu0)<=(11/10)*157435/165888 < B*.

Put L=11*5^80*7^80 and A=[1 modL]. At every x in A all81 depth4
originals match, and their ternary residues i=0,...,80 cover the entire
ternary coordinate modulo81. Thus c(x)=0 on A.

The shallow PA source has no exclusion on the first5/7 coordinates
of A, because they are1 whereas the selected phase is3. Its11-row is
unchanged there. Therefore

    nu0(A)=1/L>0.

NO supported joint probability on actual U can retain this marginal.
This is an exact failure on a supplied actual PA law, not a statement
about an arbitrary externally invented marginal.

Now use the periodic second slot, A_i={3,i mod3}. The interval proof
removes all dead fibres and bounds active cofactor count by two. This
is a different actual PA input and a different marginal. Its11-row
excludes at most the four roots0,1,2,3; its good Haar mass is at least
7/11, so normalization density is at most11/7<5/3. No PA mass loss
occurs, and later coordinates remain Haar. Thus

    R_Q(nu)<=(11/7)*157435/165888.

In this finite example each active cofactor has just e=4,5,6. Since
u=H3, its total ternary deletion is at most

    3^-4+3^-5+3^-6=13/729.

Two active cofactors leave c>=703/729. The fixed-u lift therefore has

    R_P <= (11/7)r_H +[729/(2*703)](1+(11/7)r_H)
        =649126777/233238528
        =2.783102699910711... <566/49.

This estimate includes every query height using the exact Haar density
majorant and R3(H3)=1/2. It is an upper bound, not an optimum claim.

Every actual original is irredundant. For the original at cofactor d_i
and Q color r, choose x_Q=r+d_i modulo L. Its p/q valuations relative
to r, truncated at80, are i and80-i, so it matches no other cofactor in that
color. Its residue modulo11 is r, so it matches none of the other
three colors. Choose its ternary phase by CRT. This is a private
witness. The accompanying exact program checks all324 private witnesses
against every actual original, without enumerating the enormous period.

The example proves the need and feasibility of changing the actual PA
marginal. It is not claimed to defeat every earlier actual-weighted
certificate: its large cofactors place it outside the finite shallow
window, and it also has simpler specially tailored sources. The
arbitrary-N selector theorem, rather than uniqueness of this example's
certificate, is the reusable result.

## Boundaries and reuse search

The theorem still restricts tail projections to three globally coherent
phases, a common D separating them, and a single two-coordinate exponent
antichain. Arbitrary support-dependent phases need not match intervals
or only one color. Two already compulsory shallow phases would consume
both PA slots and prevent this specific construction. Neither case is
solved here. The selector chooses phases before the PA law, not after
observing a point x.

Reports571–572 were checked for the fixed-marginal obstruction and
existing fibre-lift interface. Reports383 and451 contain different root
absorption and normalized phase-trimming constructions; they do not
supply this periodic two-slot interval selector or a complete-query
bound for it. Searches for cyclic selectors, cofactor intervals and
exponent antichains also found the different inventories of450,
478/483 and562, not this selector. No external novelty claim is made.

Artifacts: [periodic_cofactor_selector.py](../../frontier/cover-geometry/periodic_cofactor_selector.py) and [exact data](../../frontier/cover-geometry/periodic_cofactor_selector.json).
The program passed19 named exact checks, including19683 valuation
patterns,324 literal original labels and all private witnesses. These
finite checks support the stated example. The interval proof supplies
the arbitrary-N and arbitrary-height quantifiers. No new Lean verification is claimed.
