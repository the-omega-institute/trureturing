# Ternary conditioning preserves a joint query and entropy boundary

The automatic bridge to a two-copy Q-only problem is false, even for a four-class irredundant actual core, one occupied pure-3 class, and a full-support law already in [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md)'s G. An exact fibre decomposition is available, but it preserves additional 3-digits, or else it produces higher cofactor multiplicities. Its entropy and query coupling must be retained in a single global law.

These are ordinary mathematical results and exact finite arithmetic, not new Lean verification or a resolution of unrestricted Erdős #7. The remaining same-law mixed-query bound is not proved.

Throughout, H is product Haar probability, alpha=7235955529/6075000000000 and Lambda=1/alpha. The fixed irredundant original core is M0, with the complete actual survivor U. As in report534, G consists of supported laws nu with nu<=Lambda H and R_unused(nu)+KL(nu||H)<=log Lambda; unused means outside the global M0 at every query height.

## Existing results and the missing premise

- [Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) section 3 obtains a two-copy problem on primes excluding 3 from a **3-flat** original family. Its direct capped-law theorem constructs a new law on a two-copy survivor; it does not identify that law with a conditional of an arbitrary report534 G-law.
- [Report380](380-small-prime-survivors-and-original-haar-costs.md) HB6 and [report381](381-repeated-prime-exposure-in-missing-fibres.md) RE1 retain arbitrary heights when restricting one prime root, precisely by keeping all higher digits. Positive output prime exponents then have a unique input predecessor; only exponent zero can receive two numerical labels.
- [Report388](388-saturated-chain-blockers-do-not-supply-conditional-caps.md) rules out automatic full-history conditional caps from certain abstract tree and marginal hypotheses. Its source is abstract, so it does not itself establish the actual-family obstruction proved here.
- [Report523](523-correlated-unit-conditioning-pays-generated-rectangle-defects.md) supplies a usable model for correlated conditioning: keep one actual joint law and charge the generated rectangle defect to the same account. It supplies no zero-defect or automatic Gibbs-budget inheritance.
- `D5/S3/Arith/Congruence/PurePrefixResidualLaw.lean`, theorem `exists_exact_residual_law`, computes the actual forbidden-prefix complement and conditional cylinder probabilities after ancestor pruning. It concerns a pure one-coordinate prefix family, not mixed cofactor multiplicity or preservation of report534's G.

The following construction preserves every original numerical label and its fixed phase throughout. No law supplied by these references is substituted independently on a fibre.

## Exact one-digit transport

Write P={3} union Q, Q={5,7,11,13,17,19}. Decompose an original modulus as m=3^a d with d Q-smooth. Fix the first ternary root r and use the coordinate map

    x_3=r+3y_3,       x_Q=y_Q.

If a=0, the original remains one class of modulus d. If a>=1, it is inactive unless its fixed 3-root is r; when active, its pullback is the single class of modulus 3^(a-1)d with the original higher 3-digits and original Q-phase.

Hence an output modulus containing 3 has at most one input label, while an output Q-only modulus d can receive at most the two input labels d and 3d. But the output still has a 3-coordinate whenever any active original has a>=2. Only the separate 3-flat premise makes this a two-copy problem entirely on Q. A selected root could also work if every active label above height one is absent, but this is another premise, not a consequence of irredundancy.

If the selected root has an actual survivor, no pure-3 original can become an active unit-modulus class covering that entire fibre. This is also needed when applying a nonunit two-copy theorem.

Applying the operation repeatedly does not preserve multiplicity two after all 3-digits are removed. Different original 3-heights can ultimately collide at the same Q-cofactor.

## An actual shallow four-class counterexample

Take the fixed originals

    1 mod3,
    0 mod15,
    36 mod45,
    27 mod135.

The last three have ternary prefixes 0 at depths 1,2,3, and mod-5 phases 0,1,2 respectively. The pure-3 original lies in root 1. Thus all four classes are pairwise disjoint, so each is essential to its actual union; private witnesses are 1,0,36,27 respectively. The original core is already irredundant. Every modulus is at most 135, hence these mixed labels are in report534's shallow residual inventory.

On the full period 135 their union has 45+9+3+1=58 points, and the complete actual survivor U has 77 points. Let nu=H|U/h, h=77/135, with Haar tails on every unused coordinate. The full original ternary fibre x_3=0 mod27 has five mod-5 points. Its original mixed holes have phases 0,1,2, leaving phases 3,4. Its mass under the SAME nu is

    nu(x_3=0 mod27)=2/77>0.

The active Q-family therefore has **three** different residues of the same numerical modulus 5. It is not an admissible two-copy input to report348. The labels 15,45,135 remain distinct in the original objective; silently calling all three one or two copies loses their identity.

This law is in G. Put E_P=product_(p in P) p/(p-1). Uniform survivor conditioning gives q_d(nu)<=1/(hd) for every nonunit P-smooth label, including every depth. Also D_H(nu)=-log h<=1/h-1. Thus

    R_unused(nu)+D_H(nu)
      <=(E_P-1)/h+1/h-1
      =E_P/h-1=16899/4096<5.

The retained Lambda exceeds 3^6; since e<3, log Lambda>6. Therefore the entropy-query budget is satisfied strictly. The density 135/77 is below Lambda, and nu has full actual survivor support. This is an actual common-G-law example, not a combination of separately favorable laws.

The example is not close to refuting the desired total query bound; it refutes only automatic two-copy inheritance. A specially chosen law could avoid this fibre, but choosing it requires a new common-law argument.

## Unbounded active multiplicity and conditional density

The same obstruction holds at arbitrary heights. Let d=5^r with r>=1, choose 1<=k<d, and take the originals

    C_pure={x_3=1 mod3},
    C_j={x_3=0 mod3^j, x_Q=j-1 modd},  1<=j<=k.

The numerical modulus of C_j is 3^j d. All phases are fixed once. Distinct mod-d phases make the mixed originals disjoint, and their ternary root 0 makes them disjoint from C_pure. They form an irredundant actual core with

    h=H(U)=2/3-(1-3^(-k))/(2d)>17/30.

The full ternary fibre 0 mod3^k has exactly k active classes at the same cofactor d and positive survivor mass. Its conditional Q-law under the uniform global survivor law is uniform on d-k mod-d classes, with density

    d/(d-k)

relative to H_Q. The global uniform law remains in G uniformly: its density is less than 30/17 and

    R_unused+D_H<=E_P/h-1<E_P/(17/30)-1<5<log Lambda.

Taking k=d-1 and increasing r makes the conditional density unbounded while retaining this global G-law. Already d=3125, k=3124 gives conditional density 3125>Lambda and conditional entropy log3125>logLambda. Consequently neither the global Haar cap nor the original entropy budget descends unchanged to every positive-mass full ternary fibre.

No large family or period was enumerated for this general construction. Its mixed labels above 10^9 are, of course, globally paid by report534's retained tail. This all-height obstruction does not invalidate that payment; it shows why conditioning the already paid global law cannot inherit its numerical cap for free.

## Exact disintegration that preserves one law

Let h3 be an integer at least the largest original 3-exponent, and set N=3^h3. All original constraints depend on the ternary coordinate only through t modN. One may average a law in G over translations in N Z_3. This leaves U invariant and preserves the complete original phases; cylinder maxima and entropy are convex, so averaging does not increase any retained objective or entropy, and preserves the Haar cap. This produces Haar tails beyond height h3. This averaging is a simultaneous operation on the entire law, not a fresh choice for each query.

Such a law has the form

    nu=sum_(t modN) lambda_t [delta_t times Haar_3_tail times kappa_t],

with lambda_t>=0 and sum lambda_t=1. Every positive-weight kappa_t is supported on the actual Q-fibre U_t, including every original label active at t. Its entropy satisfies the exact chain rule

    D_H(nu)=sum_t lambda_t log(N lambda_t)
                +sum_t lambda_t D_(H_Q)(kappa_t).

The density cap is equivalently

    lambda_t (d kappa_t/dH_Q)<=Lambda/N

almost everywhere on each positive-weight fibre. It permits a conditional cap Lambda/(N lambda_t), not the original Lambda. The counterexample above realizes this mechanism with a small positive lambda_t.

For 0<=a<=h3 and every Q-smooth d, the complete original query has the exact value

    q_(3^a d)(nu)
      =max_(r mod3^a, b modd)
          sum_(t congruent r mod3^a) lambda_t kappa_t([b]_d).

For a>h3, Haar tails give

    q_(3^a d)(nu)=3^(h3-a) max_t lambda_t q_d(kappa_t).

The formula includes a=0: one **same** global phase b is used across every fibre. Replacing max_b of this sum by a sum of separately optimized maxima is only an upper bound and may be strict. Likewise, separately choosing kernels to minimize each original-label response need not provide one family of kernels satisfying all queries and the entropy budget.

For a proposed family of glued kernels, the support requirements above, the pointwise weighted density inequalities, and

    sum_(nonunit labels m not in M0) q_m(nu)
      +sum_t lambda_t log(N lambda_t)
      +sum_t lambda_t D_(H_Q)(kappa_t)
      <=log Lambda

are an exact test for G-membership. Here every q_m is the displayed global expression indexed by its original numerical m, and M0 is the fixed irredundant core. A local “unused” classification cannot replace this original global classification.

If these conditions hold and the shallow mixed sum of the same displayed q_m is less than 51863873/25500000, report534 applies with its pure-chain entropy charged once. No new entropy charge per fibre is required or permitted. Conversely, report348's existence of local capped laws alone proves neither this entropy inequality nor the required small residual sum.

## A finite quantitative sufficient gluing certificate

The exact conditions above can be certified by finitely many conditional caps plus one analytic reciprocal tail; no independently optimized conditional law is inferred. Fix proposed kernels kappa_t and weights lambda_t, all simultaneously, with kappa_t supported on U_t whenever lambda_t>0. Choose numbers D_t>=1 and e_t>=0 such that

    kappa_t<=D_t H_Q,      D_(H_Q)(kappa_t)<=e_t.

For a finite numerical cofactor cutoff D>=1, give simultaneous caps

    q_d(kappa_t)<=b_(t,d),   for Q-smooth 1<=d<=D,
    b_(t,1)=1.

Each row of b must belong to its one proposed kappa_t. One sufficient entropy bound is e_t=log D_t; a better actual entropy bound may be used. Zero-weight rows may be filled arbitrarily because they contribute nowhere.

For vectors z=(z_t), define the finite prefix envelope

    A_a(z)=max_(r mod3^a) sum_(t congruent r mod3^a) lambda_t z_t,
                  0<=a<=h3.

Thus A_0(z)=sum_t lambda_t z_t and A_h3(z)=max_t lambda_t z_t. Let

    tau_Q(D)=sum_(Q-smooth d>D)1/d.

The original global unused-query sum is bounded by the explicit number

    C_unused =
      sum_(a=0)^h3 sum_(Q-smooth d<=D,
                       3^a d>1, 3^a d not in M0) A_a(b_d)
      +(1/2) sum_(Q-smooth d<=D) A_h3(b_d)
      +tau_Q(D) [sum_(a=0)^h3 A_a(D_vector)+(1/2)A_h3(D_vector)].

Proof: for a<=h3, the exact common-phase formula is bounded above by A_a((q_d(kappa_t))_t). For d>D, apply the simultaneous density caps D_t/d. Every label at a>h3 is unused because h3 is at least the maximum original ternary height, and its exact Haar-tail multiplier sums to sum_(a>h3)3^(h3-a)=1/2. The unit cofactor is included in this latter term because it represents nonunit pure powers of 3. The tail term can conservatively use any certified upper bound for tau_Q(D), including tau_P(D); no new label enumeration is required if such a bound is already retained.

Consequently the finite inequalities

    lambda_t D_t<=Lambda/3^h3       for every t,

    C_unused +sum_t lambda_t log(3^h3 lambda_t)
             +sum_t lambda_t e_t <=log Lambda

are sufficient to place the **glued one law** in G. Conventions at lambda_t=0 are the usual 0 log0=0.

If D also contains every Q-cofactor of the original shallow mixed labels, their SAME-law cost is at most the finite expression

    C_mixed =sum_(3^a d in M0, 3^a d<=10^9, omega(3^a d)>=2)
                   A_a(b_d).

All these a are at most h3. Thus C_mixed<51863873/25500000 together with the preceding support, density and entropy certificate suffices to close report534's remaining route. This is a concrete sufficient test, not an assertion that feasible rows and weights with this bound exist. The use of A_a may overpay because it allows different conditional maximizing phases; the exact common-phase formula can replace it whenever phase-resolved data are available.

In the arbitrary-multiplicity construction, k original labels project to the same cofactor d, and their k phase values are distinct because k<d. With a fixed cofactor d the number of distinct phase values is bounded by d, even though repeated original labels could be more numerous. The construction takes d=5^r increasing to obtain unbounded distinct phases without conflating these two counts.

## Finite verification and remaining premise

The [fixed consumer](../../frontier/cover-geometry/ternary_fiber_transport.py) and its [result](../../frontier/cover-geometry/ternary_fiber_transport.json) check the four-class counterexample on its135-point period, the positive same-law fibre and the rational bounds placing the uniform law in G. All14 checks passed. The general multiplicity construction and the gluing formulas are proved above; the finite check does not establish their arbitrary-height statements.

A theorem supplying simultaneous conditional laws and prefix weights with C_mixed below delta remains missing. The exact interface preserves global numerical labels, their activated phases, the common prefix weights and one entropy budget; local two-copy laws by themselves do not supply that interface.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/ternary_fiber_transport.py
```
