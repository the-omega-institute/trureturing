# SixRowCoupling

## Abstract

The literal independently labelled K6 family couples the existing head witness to its actual twenty-one-deficit tail assignment at one unchanged vector. A direct APPT consumer transports the first fifteen and last twenty-one spectrum entries into this family.

For arbitrary U > 0, r >= 0, nonnegative h and boxed monotone d of mass at most six, the generic supplier premise is PSD of K(U(1+r+h(pi E)), U(1-d(sigma B))) for every independent pair of genuine pool bijections. This is an interface to a literal matrix family, not an assumed scalar bound. SixRowHead.head_exists supplies one nonnegative unit p and one fifteen-edge bijection. SixRowTail.tail_exists supplies a complete twenty-one-slot bijection at exactly that p.

For z=(1,p), finite expansion of the actual K entries gives z transpose K z = 2U(2 - headValue(r+h,p,pi) - tailCharge(d,p,sigma)). Each unordered edge occurs twice. PSD and U > 0 bound the sum of the two charges by two, giving sqrt(sum(r+h)^2) + q/2 <= two. Its right-hand margin is nonnegative, so squaring yields a + 2rH + 15r squared <= (2 - q/2) squared, with a=sum h squared, H=sum h and q=sum d squared.

The literal consumer assumes n >= 23, an actual product-basis equivalence, a nonnegative antitone spectrum, APPT of its actual diagonal, and positivity of U=lambda[6n-21]. It sets b=lambda[14], r=(b-U)/U, h_i=(lambda[i]-b)/U and d_j=(U-lambda[6n-21+j])/U. The finite transport reuses literal_assignment_psd with independent permutations formed through Fintype.equivFin and finCongr of the actual 15/21 cardinalities. Every transported entry is proved equal to the actual spectrum entry by the two normalization identities. K_charge on the all-ones vector derives D <= 6 before the head and tail witnesses are selected. Spectrum ordering and nonnegativity supply the other signs and the d box. Unit trace is not required by this homogeneous consumer; scale positivity remains the explicit hypothesis to be supplied by the existing physical head result.

The head estimate selects one vector. The tail estimate assigns the bottom labels at that same vector, and the literal APPT family supplies a positive semidefinite test for the combined assignment.

**Theorem 1.1 (literal same-vector quadratic identity).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.quadratic_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.quadratic_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quadratic_identity (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ) (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21) (hn : ∑ i, (p i)^2=1) : (Fin.cases 1 p : Fin 6 → ℝ) ⬝ᵥ (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))) *ᵥ (Fin.cases 1 p : Fin 6 → ℝ) = 2*U*(2-SixRowHead.headValue (fun i => r+h i) p π-tailCharge d p σ)

**Theorem 1.2 (independently labelled matrix supplier coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.family_coupled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.family_coupled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem family_coupled (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ) (hU : 0 < U) (hr : 0 ≤ r) (hh : ∀ i, 0 ≤ h i) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (hdo : Monotone d) (hm : ∑ i, d i ≤ 6) (hf : ∀ (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21), (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))).PosSemidef) : Real.sqrt (∑ i, (r+h i)^2)+(∑ i, (d i)^2)/2 ≤ 2 ∧ (∑ i, (h i)^2)+2*r*(∑ i, h i)+15*r^2 ≤ (2-(∑ i, (d i)^2)/2)^2

**Theorem 1.3 (actual-spectrum APPT coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.literal_coupled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.literal_coupled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_coupled (n : ℕ) (hn : 23 ≤ n) (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ) (hl : Antitone l) (h0 : ∀ i, 0 ≤ l i) (happt : APPT (diagonal (fun z => (l (e z) : ℂ)))) (hU : 0 < l ⟨6*n-21,by omega⟩) : let U := l ⟨6*n-21,by omega⟩; let b := l ⟨14,by omega⟩; let r := (b-U)/U; let h : Fin 15 → ℝ := fun i => (l ⟨i.val,by omega⟩-b)/U; let d : Fin 21 → ℝ := fun j => (U-l ⟨6*n-21+j.val,by omega⟩)/U; Real.sqrt (∑ i, (r+h i)^2)+(∑ j, (d j)^2)/2 ≤ 2 ∧ (∑ i, (h i)^2)+2*r*(∑ i, h i)+15*r^2 ≤ (2-(∑ j, (d j)^2)/2)^2

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.family_coupled`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.literal_coupled`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling.quadratic_identity`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail](SixRowTail.md)
