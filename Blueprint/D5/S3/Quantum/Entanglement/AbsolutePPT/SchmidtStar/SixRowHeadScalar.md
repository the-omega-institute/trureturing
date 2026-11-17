# SixRowHeadScalar

## Abstract

The scalar estimate uses the explicit quarter-circle recipe with alpha at least one half, k between zero and one, and h between zero and three halves. The half-angle substitution reduces it to the exact polynomial certificate. Both squaring steps compare nonnegative quantities, and every divided denominator is positive.

The scalar estimate uses the explicit quarter-circle recipe with alpha at least one half, k between zero and one, and h between zero and three halves. The half-angle substitution reduces it to the exact polynomial certificate. Both squaring steps compare nonnegative quantities, and every divided denominator is positive.

**Theorem 1.1 (half angle bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem half_angle_bound (z k h : ℝ) (hz : 0 < z) (hz' : z ≤ 3/4) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) (hg : 0 ≤ constraint z k h) : let s := (1-z^2)/(1+z^2) let t := 2*z/(1+z^2) let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (1+k*h+t^2*k) ≤ s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T)

**Theorem 1.2 (unit bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.unit_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.unit_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem unit_bound (s t k h : ℝ) (hs : 0 ≤ s) (ht : 0 < t) (hn : s^2+t^2=1) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) (hcap : t^2 ≤ 4*s^2*(1+k*h)) : let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (1+k*h+t^2*k) ≤ s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T)

**Theorem 1.3 (recipe bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.recipe_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.recipe_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem recipe_bound (alpha k h : ℝ) (ha : 1/2 ≤ alpha) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) : let L := Real.sqrt (alpha^2+1+k*h) let s := alpha/L let t := Real.sqrt (1+k*h)/L let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (alpha^2+1+k+k*h) ≤ alpha*s+t*T+t^2*(1+s)*k*h/(2*T)

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.recipe_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.unit_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate](SixRowHeadCertificate.md)
