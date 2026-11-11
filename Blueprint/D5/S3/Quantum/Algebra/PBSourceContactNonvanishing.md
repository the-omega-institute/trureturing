# Nonvanishing of the original source readout

## Abstract

Quantitative source nonvanishing on the original complete two-coordinate actor contact model, including both source signs and both actor axes.

The actor is the entire complex two-coordinate vector space. Its squared Euclidean norm is the sum of the two squared coordinate norms. The fixed operators are C=diag(1,2), H=2C+hJ and B=H+C, where J exchanges the two coordinates. The fixed source is (1/sqrt(2),r), with r either 1 or -1. The parameters x,y,h are real, abs(y)>1 and abs(h)<1. The orientation here is the source's fixed positive imaginary unit; both signs of y remain in scope.

The Contact predicate retains the actual vectors u,p,q,a and the complex source amplitude eta. It imposes the original unit norm, both real diagonal graph pairings, the full mixed graph equality, q=(ell I+2 C inverse)p+i B C u, a=i(I-ell C inverse)p, and the two coordinates of a-Hu+ell C squared u/2=eta times the same fixed source. Here ell=x+iy. The displayed coordinate functions are these literal two-dimensional operators; no axis is removed and neither coordinate of u nor x is divided out.

**Theorem 1.1 (The full quantitative source bound).**

$$\forall h \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall u \in Vec,\; \forall p \in Vec,\; \forall q \in Vec,\; \forall a \in Vec,\; \forall eta \in \mathbb{C},\; \operatorname{Contact}\left(h, r, x, y, u, p, q, a, eta\right) \Rightarrow \left(\operatorname{sourceReadout}\left(r, x, y, u\right) \ne 0 \land \left(\operatorname{sqrt}\left(2\right) \cdot \left(1 + 3 \cdot \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(u, 1\right)\right), 2\right) - \operatorname{abs}\left(h\right)\right) \le \operatorname{norm}\left(eta\right) \land 0 < \operatorname{norm}\left(eta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.original_contact_nonvanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source readout is u adjoint times (C-ell I) inverse times C times the fixed source. It is nonzero. The norm of eta is at least sqrt(2) times (1+3 norm(u second coordinate) squared-abs(h)), and is strictly positive. The proof uses the actual source equation and graph constraints to obtain eta times the source readout equal to the original residual numerator. The signed imaginary part of that numerator is bounded below by 3+9 norm(u second coordinate) squared-3 abs(h), while abs(y) times the norm of the source readout is at most 3/sqrt(2).

This is the quantitative nonvanishing clause of the original actual-contact reduction. It does not establish the converse reconstruction, the projective phase quotient, the complete finite-environment PB threshold, an attaining contact, the strict descent theorem, or the opposite imaginary orientation's conjugation transport. The mathematical model keeps the source fixed; it makes no physical acquisition or preparation claim.

The source-bound four-slot registration remains unfinished at https://github.com/the-omega-institute/trureturing/issues/29263. The required original-contact witness, whole-family variation and exact source occurrence ties have not been supplied; the mathematical Lean proof does not establish registration completion.

**Theorem 1.2 (Exact four-real reduction for the fixed source contact).**

$$\forall h \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall u \in Vec,\; \forall eta \in \mathbb{C},\; \left(r = 1 \lor r = -1\right) \Rightarrow \left(\operatorname{abs}\left(h\right) < 1 \Rightarrow \left(1 < \operatorname{abs}\left(y\right) \Rightarrow \left(\operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(u, 0\right)\right), 2\right) + \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(u, 1\right)\right), 2\right) = 1 \Rightarrow \left(\operatorname{Contact}\left(h, r, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right), \operatorname{qFormula}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right), \operatorname{aFormula}\left(x, y, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right), eta\right) \Leftrightarrow \left(\operatorname{reducedMass}\left(h, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(\operatorname{reducedReal}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(\operatorname{reducedImag}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land eta \cdot \operatorname{sourceReadout}\left(r, x, y, u\right) = \operatorname{numerator}\left(h, x, y, u\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.contact_iff_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real h,r,x,y, a unit two-coordinate vector u and a complex amplitude eta, the displayed pFormula determines the two actor coordinates, while qFormula and aFormula retain the literal graph and actor equations. Under r equal to 1 or -1, abs(h)<1, abs(y)>1 and the unit equation, the complete Contact predicate is equivalent to the four reduced clauses: the complex mass equation, the real mixed equation, the imaginary second-graph equation and the source balance eta times sourceReadout equals numerator.

The forward direction extracts the mass and balance identities from the original contact and takes the real and imaginary parts of the two graph equations. The reverse direction reconstructs the Contact fields with the displayed formulas; the source coordinates are verified by the two nonzero resolvent denominators, and the remaining graph conditions follow exactly from the reduced clauses. This is a fixed-coordinate equivalence with both axes retained.

The theorem does not assert sourceReadout nonvanishing, a projective phase quotient, the complete finite-environment threshold, an attaining contact, the strict descent theorem, or transport to the opposite imaginary orientation. Those claims remain outside this declaration.

**Theorem 1.3 (The full contact characterization).**

$$\forall h \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall u \in Vec,\; \forall p \in Vec,\; \forall q \in Vec,\; \forall a \in Vec,\; \forall eta \in \mathbb{C},\; \left(r = 1 \lor r = -1\right) \Rightarrow \left(\operatorname{abs}\left(h\right) < 1 \Rightarrow \left(1 < \operatorname{abs}\left(y\right) \Rightarrow \left(\operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(u, 0\right)\right), 2\right) + \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(u, 1\right)\right), 2\right) = 1 \Rightarrow \left(\operatorname{Contact}\left(h, r, x, y, u, p, q, a, eta\right) \Leftrightarrow \left(p = \operatorname{pFormula}\left(h, x, y, r, u, eta\right) \land \left(q = \operatorname{qFormula}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(a = \operatorname{aFormula}\left(x, y, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(\operatorname{sourceReadout}\left(r, x, y, u\right) \ne 0 \land \left(\operatorname{reducedMass}\left(h, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(\operatorname{reducedReal}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land \left(\operatorname{reducedImag}\left(h, x, y, u, \operatorname{pFormula}\left(h, x, y, r, u, eta\right)\right) \land eta \cdot \operatorname{sourceReadout}\left(r, x, y, u\right) = \operatorname{numerator}\left(h, x, y, u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.contact_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed source signs, small h, nonzero imaginary parameter and a unit vector, an arbitrary Contact tuple is equivalent to the explicit pFormula, qFormula and aFormula fields together with sourceReadout nonvanishing, the three reduced clauses and the source balance.

The forward direction uses the source-column inversion, the exact four-real reduction and the quantitative nonvanishing theorem. The reverse direction applies contact_iff_reduced after the three field equalities. The finite environment, phase quotient and remaining continuation claims are not inferred.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.contact_characterization`
- Truth anchor: `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.contact_iff_reduced`
- Truth anchor: `D5/S3/Quantum/Algebra/PBSourceContactNonvanishing.original_contact_nonvanishing`
