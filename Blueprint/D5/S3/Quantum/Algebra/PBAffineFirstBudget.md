# Original affine PB budgets

## Abstract

The same original total response satisfies the affine first-label budget of source 162.2. Its two P2 estimates use one functional and the complete actual PB outer labels.

**Theorem 1.1 (Leading scalar budgets).**

$$\forall c \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall pzero \in \mathbb{R},\; \forall pone \in \mathbb{R},\; \forall ptwo \in \mathbb{R},\; \forall qzero \in \mathbb{R},\; \forall qone \in \mathbb{R},\; \forall qtwo \in \mathbb{R},\; \left(\forall a \in \mathbb{R},\; \operatorname{abs}\left(c - a \cdot d\right) \le \operatorname{sqrt}\left(pzero + 2 \cdot a \cdot pone + \operatorname{pow}\left(a, 2\right) \cdot ptwo\right) + \operatorname{sqrt}\left(qzero + 2 \cdot a \cdot qone + \operatorname{pow}\left(a, 2\right) \cdot qtwo\right)\right) \Rightarrow \operatorname{abs}\left(d\right) \le \operatorname{sqrt}\left(ptwo\right) + \operatorname{sqrt}\left(qtwo\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.leading_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real coefficients, the affine absolute-value bound implies the leading square-root bound. Reciprocal positive scaling and continuity include zero leading coefficients.

**Theorem 1.2 (The shared-direction Gram expansion).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall phi \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \forall A \in E,\; \forall B \in E,\; \forall n \in E,\; \forall theta \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \left(\forall x \in E,\; \forall y \in E,\; \operatorname{apply}\left(J, x, y\right) = \operatorname{apply}\left(J, y, x\right)\right) \Rightarrow \operatorname{gram}\left(J, phi, A + \operatorname{smul}\left(alpha, n\right), B + \operatorname{smul}\left(theta \cdot alpha, n\right)\right) = \operatorname{gram}\left(J, phi, A, B\right) + 2 \cdot alpha \cdot \left(theta \cdot \operatorname{apply}\left(phi, \operatorname{apply}\left(J, A, A\right)\right) \cdot \operatorname{apply}\left(phi, \operatorname{apply}\left(J, n, B\right)\right) + \operatorname{apply}\left(phi, \operatorname{apply}\left(J, n, A\right)\right) \cdot \operatorname{apply}\left(phi, \operatorname{apply}\left(J, B, B\right)\right) - \operatorname{apply}\left(phi, \operatorname{apply}\left(J, A, B\right)\right) \cdot \left(\operatorname{apply}\left(phi, \operatorname{apply}\left(J, n, B\right)\right) + theta \cdot \operatorname{apply}\left(phi, \operatorname{apply}\left(J, n, A\right)\right)\right)\right) + \operatorname{pow}\left(alpha, 2\right) \cdot \operatorname{gram}\left(J, phi, n, B - \operatorname{smul}\left(theta, A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.gram_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetric bilinearity expands the affine determinant into its constant, linear and quadratic terms; the cubic and quartic terms cancel.

**Definition 1.3 (Projection off one real line).**

$$\forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall eta \in H,\; \forall z \in H,\; \operatorname{realPerp}\left(eta, z\right) = z - \operatorname{smul}\left(\operatorname{inner}\left(eta, z\right), eta\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBAffineFirstBudget.realPerp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a unit eta this real-linear map removes its real inner-product component. In a complex representation the removed line is real, not complex.

**Theorem 1.4 (Both ends of a norm budget).**

$$\forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall r \in \mathbb{R},\; \forall A \in \mathbb{R},\; \forall w \in H,\; \forall zp \in H,\; \forall zm \in H,\; \left(\left(\left(r = 0 \Rightarrow False\right) \land \operatorname{norm}\left(w\right) = 1\right) \land \left(\forall t \in \mathbb{R},\; 2 \cdot \operatorname{abs}\left(r\right) \cdot \operatorname{abs}\left(t + A\right) \le \operatorname{norm}\left(zp - \operatorname{smul}\left(r \cdot t, w\right)\right) + \operatorname{norm}\left(zm + \operatorname{smul}\left(r \cdot t, w\right)\right)\right)\right) \Rightarrow 2 \cdot r \cdot A = \operatorname{inner}\left(w, zm\right) - \operatorname{inner}\left(w, zp\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.two_ended_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit leading direction and the budget for every real t force equality of the two first-order norm corrections. Reciprocal scaling makes zero a differentiable minimum.

**Definition 1.5 (The shared-readout Gram determinant).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall phi \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \forall a \in E,\; \forall b \in E,\; \operatorname{gram}\left(J, phi, a, b\right) = \operatorname{apply}\left(phi, \operatorname{apply}\left(J, a, a\right)\right) \cdot \operatorname{apply}\left(phi, \operatorname{apply}\left(J, b, b\right)\right) - \operatorname{pow}\left(\operatorname{apply}\left(phi, \operatorname{apply}\left(J, a, b\right)\right), 2\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBAffineFirstBudget.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J is the original real bilinear Jordan product; phi is a real-linear reading of the original labels. No normalization, nonzero mass or strict Gram positivity is required.

**Theorem 1.6 (The actual first affine budget, source 162.2).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall u \in E,\; \forall h \in E,\; \forall p \in E,\; \forall q \in E,\; \forall D \in \operatorname{Function}\left(E, E, E\right),\; \forall phi \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \forall s \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall x \in E,\; \forall t \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(J, a, b\right) = \operatorname{apply}\left(J, b, a\right)\right) \land \left(\forall a \in E,\; \operatorname{apply}\left(J, u, a\right) = a\right)\right) \land \operatorname{apply}\left(J, h, h\right) = u\right) \land \operatorname{apply}\left(J, h, p\right) = 0\right) \land \operatorname{apply}\left(J, h, q\right) = 0\right) \land \operatorname{apply}\left(J, p, q\right) = 0\right) \land \operatorname{PB}\left(J, D\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \operatorname{pow}\left(\operatorname{apply}\left(phi, \operatorname{apply}\left(D, a, b\right)\right), 2\right) \le \operatorname{gram}\left(J, phi, a, b\right)\right)\right) \land \left(\forall tau \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), \operatorname{smul}\left(tau, p\right) + \operatorname{smul}\left(alpha, u + h\right)\right) = \operatorname{smul}\left(r \cdot tau, q\right)\right)\right) \Rightarrow 2 \cdot \operatorname{abs}\left(r\right) \cdot \operatorname{abs}\left(\operatorname{apply}\left(phi, \operatorname{smul}\left(t, q\right) + x - \operatorname{apply}\left(J, h, \operatorname{apply}\left(J, h, x\right)\right)\right)\right) \le \operatorname{sqrt}\left(\operatorname{gram}\left(J, phi, u + h, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) + \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right) - \operatorname{smul}\left(r \cdot t, p\right) - \operatorname{smul}\left(r \cdot \left(s + r\right) \cdot t, q\right)\right)\right) + \operatorname{sqrt}\left(\operatorname{gram}\left(J, phi, u + h, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) - \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right) + \operatorname{smul}\left(r \cdot t, p\right) - \operatorname{smul}\left(r \cdot \left(s + r\right) \cdot t, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_first_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E is any original real module, without a dimension, separability or completeness restriction. J is symmetric and unital; J(h,h)=u and J(h,p)=J(h,q)=J(p,q)=0. The same total D satisfies the full original PB identity. For this same phi, every original pair satisfies phi(D(a,b)) squared at most Bphi(a,b). The actual 161.4 supplier is D(s u+r h,t p+alpha(u+h))=rt q for all real t and alpha. These are exact hypotheses, not consequences here of raw A1-A3. The original faithful JC inclusion, accurate cone-to-state transfer and actual-anchor construction retain their upstream obligations.

In the formula g=D(s u+r h,x), k=J(h,x), v=x-J(h,k), theta=s+r and Z=(1+s theta)x+r theta k. The expression v is exactly (I-Uh)x/2 when Uh=2Lh squared-I; no projection law for D is assumed. The two anchors may independently be (e,j) and (j,-e). All real coefficients, including negative r, r=0 and theta=0, and zero or degenerate objects remain included.

At b=t p+alpha(u+h), PB uses nu=rt q-sx-rk and omega=st p+theta alpha(u+h)+g. Its actual outer pairs are (t(p+rq)-sx-rk+alpha(u+h),x+g+stp+theta alpha(u+h)) and (t(p-rq)+sx+rk+alpha(u+h),x-g-stp-theta alpha(u+h)). Applying the same phi to both original P2 budgets bounds their PB difference by the sum of their square roots. The complete PB right side is 2rt J(p,k)-2J(x,g)-2alpha r(tq+v); no commuting block is deleted.

The determinant expansion has constant term Bphi(A,B), linear term twice alpha times theta phi(J(A,A))phi(J(n,B))+phi(J(n,A))phi(J(B,B))-phi(J(A,B))(phi(J(n,B))+theta phi(J(n,A))), and quadratic term alpha squared Bphi(n,B-theta A). Cubic and quartic terms cancel for every real theta. The proof extracts the leading coefficient by setting alpha=delta inverse, multiplying by positive delta and taking delta down to zero in explicit scalar polynomials and square roots. Continuity includes a zero leading coefficient. No limit of D at varying inputs is used.

For every real alpha, a bound of abs(c-alpha d) by sqrt(p0+2alpha p1+alpha squared p2)+sqrt(q0+2alpha q1+alpha squared q2) therefore implies abs(d) at most sqrt(p2)+sqrt(q2). Substituting the two expanded Gram determinants gives the displayed actual original-D budget. Applying it to the vector readings in the next theorem gives source 163.4. This result does not assert source 163.1, the actual second frame, the complete affine commuting-zero row or the full 192.2 conclusion.

**Theorem 1.7 (The actual fixed-vector budget, source 163.4).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall u \in E,\; \forall h \in E,\; \forall p \in E,\; \forall q \in E,\; \forall D \in \operatorname{Function}\left(E, E, E\right),\; \forall R \in \operatorname{Readout}\left(H, J, u, D, \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{R}, E\right)\right)\right),\; \forall s \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall xi \in H,\; \forall eta \in H,\; \forall x \in E,\; \forall t \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(J, a, b\right) = \operatorname{apply}\left(J, b, a\right)\right) \land \left(\forall a \in E,\; \operatorname{apply}\left(J, u, a\right) = a\right)\right) \land \operatorname{apply}\left(J, h, h\right) = u\right) \land \operatorname{apply}\left(J, h, p\right) = 0\right) \land \operatorname{apply}\left(J, h, q\right) = 0\right) \land \operatorname{apply}\left(J, p, q\right) = 0\right) \land \operatorname{PB}\left(J, D\right)\right) \land \left(\forall tau \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), \operatorname{smul}\left(tau, p\right) + \operatorname{smul}\left(alpha, u + h\right)\right) = \operatorname{smul}\left(r \cdot tau, q\right)\right)\right) \land \operatorname{norm}\left(eta\right) = 1\right) \land \operatorname{op}\left(R, h, xi\right) = \operatorname{smul}\left(-1, xi\right)\right) \land \operatorname{op}\left(R, h, eta\right) = eta\right) \land \operatorname{op}\left(R, q, xi\right) = eta\right) \land \operatorname{inner}\left(eta, \operatorname{op}\left(R, p, xi\right)\right) = 0\right) \Rightarrow 2 \cdot \operatorname{abs}\left(r\right) \cdot \operatorname{abs}\left(t + \operatorname{inner}\left(eta, \operatorname{op}\left(R, x - \operatorname{apply}\left(J, h, \operatorname{apply}\left(J, h, x\right)\right), xi\right)\right)\right) \le \operatorname{norm}\left(\operatorname{op}\left(R, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) + \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right), xi\right) - \operatorname{smul}\left(\operatorname{inner}\left(eta, \operatorname{op}\left(R, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) + \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right), xi\right)\right), eta\right) - \operatorname{smul}\left(r \cdot t, \operatorname{op}\left(R, p, xi\right)\right)\right) + \operatorname{norm}\left(\operatorname{op}\left(R, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) - \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right), xi\right) - \operatorname{smul}\left(\operatorname{inner}\left(eta, \operatorname{op}\left(R, \operatorname{smul}\left(1 + s \cdot \left(s + r\right), x\right) + \operatorname{smul}\left(r \cdot \left(s + r\right), \operatorname{apply}\left(J, h, x\right)\right) - \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right), xi\right)\right), eta\right) + \operatorname{smul}\left(r \cdot t, \operatorname{op}\left(R, p, xi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_vector_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Readout R represents every original label by a symmetric real-linear operator, maps u to the identity, preserves J on the whole original domain and supplies original P2 for every vector. It is the existing PBActualOuterBudget.Readout with known subspace top, not BDerivedInterface or SectorCertificate. Complex Hilbert representations are read as real inner-product spaces. The geometric conditions are norm(eta)=1, op(h)xi=-xi, op(h)eta=eta, op(q)xi=eta and inner(eta,op(p)xi)=0. They concern the known frame, not a desired output law. No continuity of op as a function of original labels or of D is required.

Here Peta(z)=z-inner(eta,z)eta is the real perpendicular projection. The unnormalised vector xi+delta eta reads Bphi(n,W)=4 delta squared norm(Peta(op(W)xi+delta op(W)eta)) squared, while its reading of tq+v is 2delta(t+inner(eta,op(v)xi)). This uses the same vector functional for both actual budgets. Cancelling positive 2delta and taking delta down to zero only in fixed finite vector expressions gives the displayed inequality. The shared Z and every commuting block remain present.

The actual_affine_first_budget theorem is used on the live path for every positive delta. The next theorem consumes both ends of this actual budget to obtain source 163.6 for either nonzero sign of r. The remaining steps toward 163.1 are binding both actual anchors in a complex representation, ordinary complex polarization without a selfadjointness restriction, reconstruction of both corners and faithful return to E. None is silently assumed or reported complete. Full 192.2 also retains the actual second-frame and affine commuting-zero-row obligations.

**Theorem 1.8 (The original fixed-output single-anchor identity, source 163.6).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)][\operatorname{Module}\left(\mathbb{R}, E\right)]\forall H \in Type,\; [\operatorname{NormedAddCommGroup}\left(H\right)][\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right)]\forall J \in \operatorname{Bilinear}\left(\mathbb{R}, E, E, E\right),\; \forall u \in E,\; \forall h \in E,\; \forall p \in E,\; \forall q \in E,\; \forall D \in \operatorname{Function}\left(E, E, E\right),\; \forall R \in \operatorname{Readout}\left(H, J, u, D, \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{R}, E\right)\right)\right),\; \forall s \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall xi \in H,\; \forall eta \in H,\; \forall x \in E,\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{apply}\left(J, a, b\right) = \operatorname{apply}\left(J, b, a\right)\right) \land \left(\forall a \in E,\; \operatorname{apply}\left(J, u, a\right) = a\right)\right) \land \operatorname{apply}\left(J, h, h\right) = u\right) \land \operatorname{apply}\left(J, h, p\right) = 0\right) \land \operatorname{apply}\left(J, h, q\right) = 0\right) \land \operatorname{apply}\left(J, p, q\right) = 0\right) \land \operatorname{PB}\left(J, D\right)\right) \land \left(\forall tau \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), \operatorname{smul}\left(tau, p\right) + \operatorname{smul}\left(alpha, u + h\right)\right) = \operatorname{smul}\left(r \cdot tau, q\right)\right)\right) \land \left(r = 0 \Rightarrow False\right)\right) \land \operatorname{norm}\left(eta\right) = 1\right) \land \operatorname{norm}\left(\operatorname{op}\left(R, p, xi\right)\right) = 1\right) \land \operatorname{op}\left(R, h, xi\right) = \operatorname{smul}\left(-1, xi\right)\right) \land \operatorname{op}\left(R, h, eta\right) = eta\right) \land \operatorname{op}\left(R, q, xi\right) = eta\right) \land \operatorname{inner}\left(eta, \operatorname{op}\left(R, p, xi\right)\right) = 0\right) \Rightarrow r \cdot \operatorname{inner}\left(eta, \operatorname{op}\left(R, x - \operatorname{apply}\left(J, h, \operatorname{apply}\left(J, h, x\right)\right), xi\right)\right) = -1 \cdot \operatorname{inner}\left(\operatorname{op}\left(R, p, xi\right), \operatorname{op}\left(R, \operatorname{apply}\left(D, \operatorname{smul}\left(s, u\right) + \operatorname{smul}\left(r, h\right), x\right), xi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_anchor_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep exactly the preceding original-label and readout hypotheses, additionally r nonzero and norm(op(p)xi)=1. All positive and negative real r remain allowed. For every real t the preceding theorem gives the original budget. With w=op(p)xi, zplus=Peta(op(Z+g)xi) and zminus=Peta(op(Z-g)xi), reciprocal scaling converts it to 2 abs(1+delta r A) at most norm(delta zplus-w)+norm(delta zminus+w), where A=inner(eta,op(v)xi). This inequality holds for every real delta, including zero.

Subtract the left side to obtain an explicit differentiable function with a minimum at zero. Since norm(w)=1, Mathlib HasDerivAt.norm_sq and HasDerivAt.sqrt give derivatives -inner(w,zplus) and inner(w,zminus) for the two norm terms at zero. The absolute-value term has derivative 2rA there because its argument equals one. IsLocalMin.hasDerivAt_eq_zero then gives 2rA=inner(w,zminus)-inner(w,zplus). Orthogonality to eta removes the real projection, and the shared Z cancels, yielding the displayed identity. No derivative, limit, scaling law or additivity of D is used.

This is the single-anchor real identity, not a complex operator identity or source 163.1. The unit-row r=0 branch of the eventual projection theorem remains an upstream original-response supplier. Both actual anchors, complex polarization, corner reconstruction and faithful return remain to be combined. The four-slot escape audit at https://github.com/the-omega-institute/trureturing/issues/28369 is unfinished; no freezing, atom coverage or full 192.2 completion is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_anchor_identity`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_first_budget`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_vector_budget`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.gram`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.gram_shift`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.leading_budget`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.realPerp`
- Truth anchor: `D5/S3/Quantum/Algebra/PBAffineFirstBudget.two_ended_budget`
- Dependency: [D5/S3/Quantum/Algebra/PBActualOuterBudget](PBActualOuterBudget.md)
