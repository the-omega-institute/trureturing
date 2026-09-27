[Index](../../marked_head_profile.md) · [Actual law and coupling](414-same-projection-transport-controls-concentrated-sharp-sources.md) · [Exact separation and small heights](416-exact-independent-layout-tree-separation-and-actual-laws.md)

# Prefix-local disagreement extends the same actual law to every height at least seven

The **same** actual probability from report 414 satisfies

    Gamma_K(nu_K) <= 2t_K - 1/15                    (P1)

for every integer K>=7. This improves the height threshold without
changing the source, its component choices, or the independent original
phase game. Report 414's larger margin 9/100 for K>=10 remains valid.
The new information is the location of the coupling's row disagreements
within the seven-adic prefixes.

This is an ordinary analytic proof with exact rational controls, not
Lean certification. It concerns the explicit concentrated sharp sources
R_K of report 414, not arbitrary admissible sources or unrestricted
Erdős #7. The law is chosen before all original phases throughout.

## A sharper transport estimate using the actual coupling

Let (R,R_bar,Y) couple two probabilities while preserving the entire Y
coordinate. For 0<=j<=K define

    D_j = max_(z mod 7^j) P(R != R_bar, Y == z mod 7^j).

For every independently phased original-divisor layout lambda,

    |E_nu ell_lambda^2 - E_nu_bar ell_lambda^2|
      <= 3 sum_(j=0)^K (2j+1)D_j.                 (P2)

Indeed, in the ordered-pair expansion of the square, pure/pure terms
depend only on Y and have zero difference. Every consistent term with
at least one mixed label picks one row and one depth-j prefix, where j
is the maximal depth of its two labels. Its indicators can differ only
on row disagreement inside that particular prefix, of mass at most D_j.
There are exactly 3(2j+1) such ordered pairs at depth j. Inconsistent
phase intersections contribute zero. Summation proves P2 for each
literal layout, hence also bounds the difference of the two maxima.

No prefix cap or branching hypothesis is needed for P2. When the
coupling has total disagreement at most delta and depth-j prefix mass
at most b^-j, it gives D_j<=min(delta,b^-j), recovering 414's estimate.
Keeping D_j uses additional information about this coupling; it does
not create a uniform tail budget for arbitrary sources.

## Exact prefix disagreement on the full-five component

Use R_K, mu_K, and mu_bar_K exactly as in 414: mu_K selects the smaller
row at a duplicated leaf and otherwise the unique row; mu_bar_K keeps
the same uniform full-five Y marginal and relabels every leaf by row 1.
Each leaf has mass 5^-K, and disagreements are precisely non-row-1 leaves.

For a residual height h>=1, the non-row-1 counts in the actual subtrees are

    C_(i,h), i!=1: c_h = 5*3^(h-1),
    Q_h^A:          q_h = (5*3^h-7)/2,              (P3)

for the two missing pairs A=12,13 that occur here. C_(1,h) and pure
row-1 subtrees have count zero. To verify q_h, the continuing Q child
contributes q_(h-1), while the three clean children labelled 2,3,4
contribute 3c_(h-1). At height one the smaller-row convention gives
q_1=4. This recurrence for h>=2 yields P3. The clean count follows
from c_1=5 and c_h=3c_(h-1).

At depth j>=1 every actual prefix subtree is a Q tail, a clean C tail,
or a pure row-1 subtree. For 1<=j<K, a Q tail occurs at the prefix
whose first digit is zero followed by j-1 zeros; a non-row-1 C tail
occurs at first digit three followed by j-1 zeros. Thus the maximal
disagreement counts at that depth are
exactly max(c_(K-j),q_(K-j)). At leaf depth some non-row-1 leaves remain.
Together with the total count from 414 this gives

    D_0 = (25*3^(K-2)-7)/5^K,
    D_j = max(5*3^(K-j-1), (5*3^(K-j)-7)/2)/5^K,
                                             1<=j<K,
    D_K = 5^-K.                                    (P4)

For an uncomplicated all-height estimate, P4 implies

    D_0 <= (25/9)(3/5)^K,
    D_j <= (5/2)(3/5)^K 3^-j,                1<=j<=K.

Since sum_(j>=1)(2j+1)3^-j=2,

    sum_(j=0)^K (2j+1)D_j <= (70/9)(3/5)^K.         (P5)

## Pair-component disagreement separates after the first digit

For each of the three pair laws eta_23, eta_24, eta_34, the coupling
from 414 changes rows only at Y=0 and Y=1. Each of these points has
disagreement mass 1/(2*3^K). They belong to the same depth-zero cell,
but to different cells at every positive depth. Therefore its profile is

    D_0 = 3^-K,
    D_j = (1/2)3^-K,                         1<=j<=K.

Its weighted sum is exactly ((K+1)^2+1)/(2*3^K). This uses the same
actual-to-comparison coupling, not a new probability selected after
seeing a layout.

## Uniform improvement of the height threshold

The common law and its comparison remain

    nu_K = (5/13)mu_K + (8/39)(eta_23+eta_24+eta_34),
    Gamma_K(nu_bar_K) < 587/104.

The comparison probabilities may leave the source; P2 transfers their
bounds to the actual supported components. Multiply the full-component
bound P5 by 3*5/13 and the pair bound by 3*8/13. It follows that

    Gamma_K(nu_K)
      <= 587/104 + (350/39)(3/5)^K
                   + (12/13)((K+1)^2+1)3^-K.        (P6)

As t_K=3-(K+2)3^-K, the finite-target margin is at least

    37/104 - (350/39)(3/5)^K
      - [(12/13)((K+1)^2+1)+2(K+2)]3^-K.           (P7)

Each subtracted term strictly decreases for K>=7. For the quadratic
term, (K+2)^2+1 < 3((K+1)^2+1); the linear term has next/current ratio
(K+3)/(3(K+2))<1, and the geometric term has ratio 3/5. At K=7,
P7 is exactly

    16319233/236925000 > 1/15.

This proves P1 at every K>=7. Retaining the exact profile P4 instead
gives K=7 margin 85217837/1184625000. Neither bound proves failure at
smaller heights when its margin is nonpositive.

## Reproduction and remaining scope

[`prefix_local_row_transport.py`](../../frontier/cover-geometry/prefix_local_row_transport.py)
provides a generic coupling profile and validated transport certificate.
It reuses 414's actual source, probabilities and couplings; checks P4
and the pair profile at K=2,...,6; compares the old and new errors; and
checks the exact K=7 threshold. A separate small coupling is checked
against all literal height-one phases, with malformed inputs rejected.

From the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_local_row_transport.py
    python3 -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_local_row_transport.py

The induction and monotonicity above supply the unbounded quantifier;
finite checks do not. Combined with 412 and 416, successful actual laws
on this explicit family are now available at K=2,3,4 and every K>=7.
The [finite completion](418-concentrated-sharp-sources-admit-a-common-law-at-every-height.md)
closes heights 5,6, giving actual laws for this explicit family at every
K>=2. The all-source problem remains open.
