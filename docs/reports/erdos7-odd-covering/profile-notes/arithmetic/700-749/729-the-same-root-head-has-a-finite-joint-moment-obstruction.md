# The same-root head also has a finite joint-moment obstruction

This is an ordinary finite rational certificate and proof, not Lean. It
concerns one prescribed first-digit source class and one scalar sufficient
criterion. It is not a covering construction or a counterexample to the
odd covering conjecture. No conclusion at beta=1/19 follows.

## Source, objective, and finite witness

Let H be the actual 85 surviving residues modulo315 after removing

    0 mod3, 1 mod9, 0 mod5, 0 mod7,
    1 mod15, 22 mod45, 1 mod21, 16 mod63,
    3 mod35, 74 mod105, 47 mod315.

Let p be any probability on H, with independent Haar higher5/7 digits.
For j in{0,1,2}, D subset{5,7}, put d=3^j product(D) and

    B_D=product_{q in D} q/(q-1)-1,
    A(p)=sum_(j,D) B_D max_(a mod d) p[x=a mod d].

Let Gamma8(p) be the maximum for complete queries at height8,8.
Let Gamma*(p) be the supremum of the second moment of a complete query
load, over globally fixed phase choices at every numerical divisor of
9*5^E*7^F, for arbitrary finite E,F. The phase at each label is fixed
before a source row is selected.

The delivered nonnegative certificate has13 cylinder coefficients and79
query coefficients, of which59 were encoded as coherent limiting layouts
and20 as finite layouts (11 at heights6,6;9 at heights7,7). Interpret all59
coherent layouts at FINITE HEIGHT8,8 for the primary proof. Preserve each
of the20 finite layouts and append arbitrary globally fixed phases at its
missing labels up to8,8. Appending indicators only increases its squared
query load. Thus every component is realized, or conservatively bounded
below, by one complete finite query on the common period

    9*5^8*7^8=20266878515625.

The cylinder weights obey their individual B_D budgets. The total query
weight is

    52895999999961/1000000000000000 <=1653/31250.

Write g8(x) for the sum of the cylinder contribution, the59 exact
height8 coherent conditional square contributions, and the20 original
finite square contributions. Exact independent calculation gives

    min_(x in H) g8(x)
       =32169707786555332783494109/32169648437500000000000000
       =1+59349055332783494109/32169648437500000000000000 >1.

The minimizing source row is137. Therefore, for EVERY p on H,

    A(p)+(1653/31250) Gamma8(p)
       >=E_p g8
       >=32169707786555332783494109/32169648437500000000000000 >1.

Indeed each mode's weighted cylinder expectation is at most its allocated
budget times its largest cylinder probability; each query square
expectation is at most Gamma8<=Gamma*. This rules out the scalar sufficient
criterion A(p)+beta Gamma*(p)<1 for beta>=1653/31250 within this source
class. It does not rule out other source classes or sufficient criteria.

## Independent vector computation and global realizability

For a finite layout, the numerical slots are(j,e,f) with j=0,1,2 and
0<=e<=E,0<=f<=F, with f the fastest index. Its supplied first-mode label
a lies modulo b=3^j*5^[e>0]*7^[f>0]. Lift it once by CRT to a phase modulo
3^j5^e7^f with ternary component a mod3^j,5-component a mod5 and all
higher5 digits zero, and the analogous7-component. These are globally
fixed phases; no row-specific choice is involved.

For a fixed actual row x, active slots are those with x=a mod b. Their
full phases are pairwise compatible, and an ordered pair of heights
(e,f),(e',f') jointly fires with probability

    5^[-(max(e,e')-1)_+] *7^[-(max(f,f')-1)_+].

The independent checker does NOT sum ordered pairs. Put
t_q(h)=q^[-(h-1)_+], and

    delta_q(h)=t_q(h)-t_q(h+1) for h<H,
    delta_q(H)=t_q(H).

If N_hk(x) counts active slots with e<=h and f<=k, the exact square vector
is

    sum_(h,k) delta_5(h) delta_7(k) N_hk(x)^2.

This follows by expanding the square and telescoping the delta weights.
The checker computes N by a two-dimensional prefix table. It separately
checks every phase projection and286410 unordered phase pairs, verifying
that common first-mode compatibility exactly matches full CRT gcd
compatibility for the chosen lifts.

For a coherent centre a at heightH, let

    J_a(x)=1+[x=a mod3]+[x=a mod9],
    R_q(H)=1+sum_(h=1..H)(2h+1)/q^(h-1).

Its conditional square is J_a(x)^2 times R5(H) when the first5-digit
matches (otherwise1), times R7(H) when the first7-digit matches
(otherwise1). The proof uses H=8. Height7 does not suffice for this
particular coefficient list; no necessity claim about height8 is made.

## Comparison and exact evidence

The [opposite-head obstruction in Report726](726-the-exact-joint-moment-still-blocks-the-complete-scalar-gate.md)
works at beta=1/19. This same-root certificate works at the explicitly
larger beta=1653/31250. The two thresholds must not be identified. Both
results retain the complete deep union debit and prefix-Haar higher digits;
actual union credits or conditional digit sources change those assumptions.

The [retained certificate](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_same_joint_obstruction_witnesses.json)
contains only the actual same-root head and its rational coefficients.
The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_same_joint_obstruction.py)
checks every budget, reconstructs globally fixed full CRT phases, evaluates
the prefix-count squares and verifies the exact rowwise lower at common
height8. Its [retained output](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_same_joint_obstruction.json)
is reproduced with `python3 -I -S -B -O`.

The prefix-count implementation was independently derived from the initial
ordered-pair certificate computation. It also reconstructs the encoded
limiting minimum172873706451315756773/172872000000000000000 at row221
as a consistency check. That limiting computation is not needed for the
finite primary obstruction. No new Lean verification, all-beta claim or
unrestricted covering conclusion is made.
