# Actual Zeta Height Fourteen

## Abstract

Unconditional full-family height fourteen and the exact natural-occurrence inverse-square mass.

**Theorem 1.1 (Every Nontrivial Zero Has Absolute Ordinate Greater Than Fourteen).**

$$\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow 14 < \left|\operatorname{im}\left(\mathit{rho}\right)\right|$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_height_gt_fourteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex rho satisfying IsNontrivialZero rho, the conclusion is 14 < |rho.im|. The exhaustive actualData = zetaZeroData family contains both imaginary signs, and actualData.multiplicity records the positive analytic order of each distinct zero. The existing height-ten exclusion supplies u = rho.im^2 > 100 for this same complete family.

Write q = rho*(1-rho), p = rho.re*(1-rho.re), and b = Im(q). The actual open strip gives 0 < p <= 1/4, while Re(q) = u+p and b^2 = u*(1-4*p). For c = (0,30,56,90,132,182), put v = sqrt(u*(1-4*p)), z_j = u+p+c_j+i*v, F = product_j z_j^(-1), and W(u,p) = Re(F). Since b = v or b = -v, simultaneous complex conjugation identifies this weight with Re(1/(q*(q+30)*(q+56)*(q+90)*(q+132)*(q+182))) for either signed imaginary part, including b = 0.

The sector comparison works on the closed auxiliary range 0 <= p <= 1/4. With theta_j = arctan(v/(u+p+c_j)) and Theta = sum_j theta_j, each angle lies between 0 and 1/sqrt(u). Thus 0 <= Theta+theta_j <= 7/sqrt(u) < 7/10 < pi/2 for u > 100. Polar multiplication gives W(u,p) = (product_j |z_j|^(-1))*cos(Theta) > 0. Differentiation in u gives -sum_j |F/z_j|*(cos(Theta+theta_j)+(v/(2*u))*sin(Theta+theta_j)) < 0. For p < 1/4, differentiation in p gives -sum_j |F/z_j|*(cos(Theta+theta_j)-(2*u/v)*sin(Theta+theta_j)) > 0: the zero shift ensures Theta+theta_j >= theta_0 and tan(theta_0) = v/(u+p) > v/(2*u). Continuity extends the comparison to p = 1/4. Consequently W decreases with u and increases with p; 100 < u <= 196 implies W(u,p) >= W(196,0). The value p = 0 is an auxiliary boundary used for comparison; actual zeros retain 0 < p.

For s = 6,8,10,12,14 define D_s = (2*s-1)*firstLiMass/2 - Re(logDeriv xiReading s). The normalized complex xi resolvents at 1 and s, paired through the reflection permutation rho -> 1-rho, preserve every analytic multiplicity. Taking real parts and exact partial fractions therefore gives the full HasSum of multiplicity(n)*W(u_n,p_n), with total S6 = D_6/3990729600 - D_8/3555377280 + D_10/6739588800 - D_12/24711825600 + D_14/216459734400.

Evaluation of the xi logarithmic derivatives and digamma values gives S6 = 66493177/143006288128704000 + (4/12649365729)*EulerGamma - log(2)/1816214400 - (9487/40477970332800)*log(pi) + Q_6/3990729600 - Q_8/3555377280 + Q_10/6739588800 - Q_12/24711825600 + Q_14/216459734400, where Q_s = Re(-zeta'(s)/zeta(s)) = sum_n Lambda(n)/n^s is the complete von Mangoldt series. Its inclusive finite part through 64 has exactly the 27 nonzero prime-power terms 2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64. For positive Q coefficients the upper estimate includes the entire remaining series n >= 65, bounded by the integral from 64 to infinity of x^(1-s)/2, namely 1/(2*(s-2)*64^(s-2)), using Lambda(n) <= log(n) <= n/2. For negative Q coefficients the finite lower estimate uses nonnegativity of the entire omitted tail.

Rational atanh logarithm bounds for the prime bases give Q_6 <= 12633076304737/1000000000000000, 1445084153477/500000000000000 <= Q_8, Q_10 <= 174085111381/250000000000000, 2677198143/15625000000000 <= Q_12, and Q_14 <= 42538887969/1000000000000000. The public library theorem HarmonicGammaTail.eulerMascheroni_upper_128 directly supplies EulerGamma < 5772156650/10^10 < 5772157/10000000. Real.log_two_gt_d9 gives 6931471803/10000000000 < log(2); Real.pi_gt_d20 and the atanh expansion with parameter K = 12 give 2289459771/2000000000 < log(pi). These inequalities have the directions required by the signed coefficients, yielding S6 <= 72126772613108177/15194418113674800000000000000000.

If an actual zero had u <= 196, its distinct conjugate zero would have the same weight and multiplicity. Each analytic multiplicity is at least one. Positivity of every other term in the complete summable family then gives S6 >= 2*W(196,0) = 345650537/72636763553532703907200. The exact lower-minus-upper difference is 4091911135692077535684108547/349994189092536057987654937200000000000000000 > 0, a strict contradiction. Hence u > 196 for every source zero, and exhaustivity transfers 14 < |rho.im| to the original arbitrary nontrivial zero. The argument uses the complete strip family with both signs and all analytic multiplicities.

**Theorem 1.2 (Complete Natural Occurrence Inverse Square Mass at Height Fourteen).**

$$\sum_{k \in \mathbb{N}} \left(\operatorname{im}\left(\operatorname{actualZero}\left(k\right)\right)^{-1}\right)^{2} \le \frac{197}{196} \cdot \mathit{firstLiMass}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_inverse_square_mass_le_height_fourteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion is sum'_k ((((actualZero k).im)^(-1))^2) <= (197/196)*firstLiMass over every natural occurrence k, with no hypothesis. Here actualZero k = actualData.zero (actualOccurrenceEquiv k).1, and actualOccurrenceEquiv is the unchanged equivalence from Nat to the full sigma family of Fin(actualData.multiplicity n). Each distinct zero therefore occurs exactly its positive analytic multiplicity, with both imaginary signs retained.

For a source zero put u = Im(zero n)^2. The height theorem gives u > 196; the strip estimate for pairWeight rho = Re(1/(rho*(1-rho))) gives 1/u <= (197/196)/(u+1) <= (197/196)*pairWeight(zero n). Multiply by the exact analytic multiplicity and compare the complete summable inverse-square series with actual_pairWeight_hasSum, whose total is firstLiMass = 2+EulerGamma-2*log(2*sqrt(pi)). The exact actual_inverse_square_tsum_transport then carries the weighted sum through every finite multiplicity fiber and actualOccurrenceEquiv to the entire natural-index sum. The height exclusion is supplied by actual_height_gt_fourteen, so no height or mass certificate is an additional premise.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_height_gt_fourteen`
- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_inverse_square_mass_le_height_fourteen`
- Dependency: [D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics](ActualHeightFourteenNumerics.md)
