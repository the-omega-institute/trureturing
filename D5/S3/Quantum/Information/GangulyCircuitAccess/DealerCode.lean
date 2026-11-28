/- GID: D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GangulyCircuitAccess/DealerCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The witness dealer slices span the shortened graph stabilizer code. -/

/-
admission_basis: escape-witness. The fixed-line and shortened-code image
calculations establish the witness correspondence with Proposition 8(2–3)
for #35163. This correspondence is checked separately from Recovery.result.
Escape audit unfinished. The preregistration is at
https://github.com/the-omega-institute/trureturing/issues/35163.
-/

import D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial
import D5.S3.Quantum.Information.GangulyCircuitAccess.Encoding
import Mathlib.Tactic.LinearCombination

/-! The graph Pauli lift and its dealer shortening for Ganguly's Proposition 8. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GangulyCircuitAccess

open scoped BigOperators Matrix

abbrev WitnessPlayers := Config (discarded witnessDealer witnessPlayers) × Config witnessPlayers

private abbrev phase := graphPhase witnessMatrix

private def character (a : ZMod 2) : ℂ := (-1) ^ a.val

private theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a

private theorem character_add (a b : ZMod 2) :
    character (a + b) = character a * character b := by
  rcases bit_cases a with rfl | rfl
  · simp [character]
  · rcases bit_cases b with rfl | rfl
    · simp [character]
    · rw [ZModModule.add_self]
      change (-1 : ℂ) ^ (0 : ℕ) = (-1 : ℂ) ^ (1 : ℕ) * (-1 : ℂ) ^ (1 : ℕ)
      norm_num

private theorem character_sq (a : ZMod 2) : character a * character a = 1 := by
  rw [← character_add, ZModModule.add_self]
  rfl

private theorem signedEntry_cast (z : Bits 7) :
    (signedGraphEntry witnessMatrix z : ℂ) = character (phase z) := by
  simp [signedGraphEntry, character]

private theorem phase_add (z x : Bits 7) :
    phase (z + x) = phase z + phase x + (witnessMatrix *ᵥ x) ⬝ᵥ z := by
  let M := witnessMatrix
  have hs (i j : Fin 7) : M i j = M j i := by
    change witnessMatrix i j = witnessMatrix j i
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : witnessGraph.Adj i j
    · simp [h, h.symm]
    · have h' : ¬witnessGraph.Adj j i := fun hadj => h hadj.symm
      simp [h, h']
  have hd (i : Fin 7) : M i i = 0 := by
    simp [M, SimpleGraph.adjMatrix_apply]
  have hswap :
      (∑ i : Fin 7, ∑ j : Fin 7, if j < i then M i j * x j * z i else 0) =
        ∑ i : Fin 7, ∑ j : Fin 7, if i < j then M i j * x i * z j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hsplit : (M *ᵥ x) ⬝ᵥ z =
      (∑ i : Fin 7, ∑ j with i < j, M i j * x j * z i) +
      (∑ i : Fin 7, ∑ j with i < j, M i j * x i * z j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.sum_filter]
    rw [← hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hd]
    · simp [h, not_lt_of_gt h]
  rw [hsplit]
  simp only [graphPhase, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [M]
  ring

/-- In the computational basis the lift has label `(x, Mx)`: translation by
`x`, followed by the sign character of `Mx` and the scalar graph phase. -/
noncomputable def graphPauli (x : Bits 7) (ψ : Bits 7 → ℂ) (z : Bits 7) : ℂ :=
  character (phase x + (witnessMatrix *ᵥ x) ⬝ᵥ z) * ψ (z + x)

private theorem graphPauli_apply (x : Bits 7) (ψ : Bits 7 → ℂ) (z : Bits 7) :
    graphPauli x ψ z = character (phase z) * (character (phase (z + x)) * ψ (z + x)) := by
  have h : phase x + (witnessMatrix *ᵥ x) ⬝ᵥ z = phase z + phase (z + x) := by
    rw [phase_add, ← add_assoc, ← add_assoc, ZModModule.add_self, zero_add]
  rw [graphPauli, h, character_add, mul_assoc]

private theorem graphPauli_add (x y : Bits 7) (ψ : Bits 7 → ℂ) :
    graphPauli x (graphPauli y ψ) = graphPauli (x + y) ψ := by
  funext z
  simp only [graphPauli_apply, ← add_assoc z x y]
  rw [← mul_assoc (character (phase (z + x))), character_sq, one_mul]

/-- The normalized graph state has its dealer coordinate in the computational basis. -/
noncomputable def witnessGraphState (z : Bits 7) : ℂ :=
  (signedGraphEntry witnessMatrix z : ℂ) / ((Real.sqrt 128 : ℝ) : ℂ)

private theorem graphState_fixed (x : Bits 7) :
    graphPauli x witnessGraphState = witnessGraphState := by
  funext z
  simp only [graphPauli_apply, witnessGraphState, signedEntry_cast, ← mul_div_assoc,
    character_sq, one_div]
  rw [div_eq_mul_inv]

private theorem graphState_fixed_line (ψ : Bits 7 → ℂ) :
    (∀ x, graphPauli x ψ = ψ) ↔ ∃ a : ℂ, ψ = fun z => a * witnessGraphState z := by
  constructor
  · intro h
    have hzero : phase (0 : Bits 7) = 0 := by simp [graphPhase]
    refine ⟨ψ 0 * ((Real.sqrt 128 : ℝ) : ℂ), ?_⟩
    funext z
    have hz := congrFun (h z) 0
    rw [graphPauli_apply, zero_add, hzero] at hz
    have hc : character 0 = 1 := rfl
    rw [hc, one_mul] at hz
    rw [← hz, witnessGraphState, signedEntry_cast]
    have hden : ((Real.sqrt 128 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 128))
    field_simp
    linear_combination -ψ z * (character_sq (phase z))
  · rintro ⟨a, rfl⟩ x
    funext z
    have h := congrFun (graphState_fixed x) z
    rw [graphPauli] at h ⊢
    rw [mul_left_comm, h]

private def restrictPlayers (z : Bits 7) : WitnessPlayers :=
  (fun i => z i, fun i => z i)

private abbrev joinDealer (p : WitnessPlayers) (s : Fin 2) : Bits 7 :=
  fullConfig witnessDealer witnessPlayers p s

private theorem dealer_join (p : WitnessPlayers) (s : Fin 2) :
    joinDealer p s witnessDealer = (show ZMod 2 from s) := by
  rfl

private theorem restrict_join (p : WitnessPlayers) (s : Fin 2) :
    restrictPlayers (joinDealer p s) = p := by
  have hd : witnessDealer ∉ witnessPlayers := by decide
  apply Prod.ext
  · funext i
    have hi := i.property
    simp only [discarded, Finset.mem_sdiff, Finset.mem_insert, not_or] at hi
    simp [restrictPlayers, fullConfig, hi.2.1, hi.2.2]
  · funext i
    have hne : (i : Fin 7) ≠ witnessDealer := by
      intro h
      exact hd (h ▸ i.property)
    simp [restrictPlayers, joinDealer, fullConfig, hne]

private theorem join_restrict (z : Bits 7) :
    joinDealer (restrictPlayers z) (show Fin 2 from z witnessDealer) = z := by
  funext i
  by_cases hd : i = witnessDealer
  · subst i
    exact dealer_join _ _
  · by_cases ha : i ∈ witnessPlayers <;> simp [joinDealer, fullConfig, restrictPlayers, hd, ha]

private def dealerParity (z : Bits 7) : ZMod 2 := (witnessMatrix *ᵥ z) witnessDealer

/-- The player factor of the lifted Pauli when both dealer coordinates vanish. -/
noncomputable def shortenedPauli (x : Bits 7) (ψ : WitnessPlayers → ℂ) (p : WitnessPlayers) : ℂ :=
  graphPauli x (fun z => ψ (restrictPlayers z)) (joinDealer p 0)

/-- The common fixed space for exactly the labels that survive dealer shortening. -/
def witnessShortenedCode : Set (WitnessPlayers → ℂ) :=
  { ψ | ∀ x : Bits 7, x witnessDealer = 0 → dealerParity x = 0 → shortenedPauli x ψ = ψ }

private def dealerBit (s : ZMod 2) : Bits 7 := fun i => if i = witnessDealer then s else 0

private theorem join_eq_add (p : WitnessPlayers) (s : Fin 2) :
    joinDealer p s = joinDealer p 0 + dealerBit s := by
  funext i
  by_cases hd : i = witnessDealer
  · subst i
    rw [Pi.add_apply, dealer_join, dealer_join]
    exact (zero_add (show ZMod 2 from s)).symm
  · have h : joinDealer p s i = joinDealer p 0 i := by
      simp only [joinDealer, fullConfig, dif_neg hd]
      rfl
    rw [Pi.add_apply, h]
    simp [dealerBit, hd]

private theorem phase_join (p : WitnessPlayers) (s : Fin 2) :
    phase (joinDealer p s) =
      phase (joinDealer p 0) + (show ZMod 2 from s) * dealerParity (joinDealer p 0) := by
  rw [join_eq_add p s, add_comm (joinDealer p 0) _, phase_add]
  have hZero : phase (dealerBit s) = 0 := by
    simp only [graphPhase]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    have hij := (Finset.mem_filter.mp hj).2
    by_cases hd : i = witnessDealer
    · have hnd : j ≠ witnessDealer := by
        intro h
        rw [hd, h] at hij
        exact (lt_irrefl witnessDealer) hij
      simp [dealerBit, hnd]
    · simp [dealerBit, hd]
  rw [hZero, zero_add, dotProduct, Finset.sum_eq_single witnessDealer]
  · rw [show dealerBit s witnessDealer = (show ZMod 2 from s) from ite_eq_left rfl]
    exact congrArg (phase (joinDealer p 0) + ·) (mul_comm _ _)
  · intro i _ hi
    simp [dealerBit, hi]
  · simp

private theorem slice_entry (p : WitnessPlayers) (s : Fin 2) :
    dealerSlices witnessGraph witnessDealer witnessPlayers p s =
      character (phase (joinDealer p s)) / 8 := by
  have hs : Real.sqrt (2 ^ (7 - 1 : ℕ) : ℝ) = 8 := by
    convert Real.sqrt_mul_self (show (0 : ℝ) ≤ 8 by norm_num) using 1
    norm_num
  change (signedGraphEntry witnessMatrix (joinDealer p s) : ℂ) /
    ((Real.sqrt (2 ^ (7 - 1 : ℕ)) : ℝ) : ℂ) = _
  rw [hs, Complex.ofReal_ofNat, signedEntry_cast]

private theorem graphState_slice (p : WitnessPlayers) (s : Fin 2) :
    witnessGraphState (joinDealer p s) =
      dealerSlices witnessGraph witnessDealer witnessPlayers p s / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h : Real.sqrt 128 = 8 * Real.sqrt 2 := by
    rw [show (128 : ℝ) = 64 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
    have h64 : Real.sqrt 64 = 8 := by
      convert Real.sqrt_mul_self (show (0 : ℝ) ≤ 8 by norm_num) using 1
      norm_num
    rw [h64]
  rw [witnessGraphState, signedEntry_cast, slice_entry, h, Complex.ofReal_mul, Complex.ofReal_ofNat,
    div_div]

private theorem shortenedPauli_factor (x : Bits 7) (ψ : WitnessPlayers → ℂ)
    (hz : dealerParity x = 0)
    (p : WitnessPlayers) (s : Fin 2) :
    graphPauli x (fun z => ψ (restrictPlayers z)) (joinDealer p s) = shortenedPauli x ψ p := by
  have hRestrict : restrictPlayers (joinDealer p s + x) = restrictPlayers (joinDealer p 0 + x) := by
    rw [join_eq_add p s]
    have hd : witnessDealer ∉ witnessPlayers := by decide
    apply Prod.ext
    · funext i
      have hi := i.property
      simp only [discarded, Finset.mem_sdiff, Finset.mem_insert, not_or] at hi
      simp [restrictPlayers, Pi.add_apply, dealerBit, hi.2.1]
      rfl
    · funext i
      have hne : (i : Fin 7) ≠ witnessDealer := by
        intro h
        exact hd (h ▸ i.property)
      simp [restrictPlayers, Pi.add_apply, dealerBit, hne]
      rfl
  unfold shortenedPauli
  simp only [graphPauli]
  rw [hRestrict, join_eq_add p s, dotProduct_add]
  have hPair : (witnessMatrix *ᵥ x) ⬝ᵥ dealerBit s = 0 := by
    rw [dotProduct, Finset.sum_eq_single witnessDealer]
    · change dealerParity x * dealerBit s witnessDealer = 0
      rw [hz, zero_mul]
    · intro i _ hi
      simp [dealerBit, hi]
    · simp
  rw [hPair, add_zero]

private theorem shortened_column (s : Fin 2) :
    (fun p => dealerSlices witnessGraph witnessDealer witnessPlayers p s) ∈ witnessShortenedCode := by
  intro x hx hz
  funext p
  let q := restrictPlayers (joinDealer p s + x)
  have hjoin : joinDealer q s = joinDealer p s + x := by
    have hs : (joinDealer p s + x) witnessDealer = (show ZMod 2 from s) := by
      rw [Pi.add_apply, dealer_join, hx, add_zero]
    have hs' : (show Fin 2 from (joinDealer p s + x) witnessDealer) = s := hs
    simpa only [hs'] using join_restrict (joinDealer p s + x)
  have h := congrFun (graphState_fixed x) (joinDealer p s)
  rw [graphPauli, ← hjoin, graphState_slice, graphState_slice] at h
  have hden : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  rw [← mul_div_assoc, div_left_inj' hden] at h
  have hf := shortenedPauli_factor x
    (fun p => dealerSlices witnessGraph witnessDealer witnessPlayers p s) hz p s
  rw [graphPauli] at hf
  change character (phase x + (witnessMatrix *ᵥ x) ⬝ᵥ joinDealer p s) *
      dealerSlices witnessGraph witnessDealer witnessPlayers q s = _ at hf
  rw [← hf, h]

private theorem parity_reference (a : ZMod 2) :
    ∃ r : WitnessPlayers, dealerParity (joinDealer r 0) = a := by
  obtain ⟨z, hz⟩ := witness_dealer_surjective (0, a)
  have hd := congrArg Prod.fst hz
  have ha := congrArg Prod.snd hz
  refine ⟨restrictPlayers z, ?_⟩
  have hd' : (show Fin 2 from z witnessDealer) = 0 := hd
  rw [← hd', join_restrict]
  exact ha

private theorem same_parity (ψ : WitnessPlayers → ℂ) (hψ : ψ ∈ witnessShortenedCode)
    (p q : WitnessPlayers) (h : dealerParity (joinDealer p 0) = dealerParity (joinDealer q 0)) :
    character (phase (joinDealer p 0)) * ψ p = character (phase (joinDealer q 0)) * ψ q := by
  let z := joinDealer p 0
  let w := joinDealer q 0
  let x := w - z
  have hx : x witnessDealer = 0 := by
    change (w - z) witnessDealer = 0
    rw [Pi.sub_apply, show w witnessDealer = 0 from dealer_join _ _,
      show z witnessDealer = 0 from dealer_join _ _, sub_self]
  have hz : dealerParity x = 0 := by
    simp only [dealerParity, x, Matrix.mulVec_sub, Pi.sub_apply, sub_eq_zero]
    exact h.symm
  have hzw : z + x = w := by simp [x]
  have hfix := congrFun (hψ x hx hz) p
  unfold shortenedPauli at hfix
  rw [graphPauli_apply] at hfix
  change character (phase z) * (character (phase (z + x)) * ψ (restrictPlayers (z + x))) =
    ψ p at hfix
  rw [hzw, show restrictPlayers w = q from restrict_join _ _] at hfix
  rw [← hfix, ← mul_assoc, character_sq, one_mul]

private theorem code_image :
    Set.range (fun v : Fin 2 → ℂ => dealerSlices witnessGraph witnessDealer witnessPlayers *ᵥ v) =
      witnessShortenedCode := by
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩ x hx hz
    funext p
    have h0 := congrFun (shortened_column 0 x hx hz) p
    have h1 := congrFun (shortened_column 1 x hx hz) p
    simp only [shortenedPauli, graphPauli] at h0 h1 ⊢
    simp only [show ∀ (W : Matrix WitnessPlayers (Fin 2) ℂ) (q : WitnessPlayers),
      (W *ᵥ v) q = W q 0 * v 0 + W q 1 * v 1 from
      fun W q => by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two], mul_add, ← mul_assoc]
    rw [h0, h1]
  · intro hψ
    obtain ⟨p0, hp0⟩ := parity_reference 0
    obtain ⟨p1, hp1⟩ := parity_reference 1
    let a := character (phase (joinDealer p0 0)) * ψ p0
    let b := character (phase (joinDealer p1 0)) * ψ p1
    let v : Fin 2 → ℂ := fun s => if s = 0 then 4 * (a + b) else 4 * (a - b)
    refine ⟨v, ?_⟩
    funext p
    have h1 : phase (joinDealer p (1 : Fin 2)) =
        phase (joinDealer p 0) + dealerParity (joinDealer p 0) := by
      rw [phase_join]
      rw [show (show ZMod 2 from (1 : Fin 2)) = 1 from rfl, one_mul]
    have hp : dealerParity (joinDealer p 0) = 0 ∨ dealerParity (joinDealer p 0) = 1 := by
      exact bit_cases _
    change (∑ s, dealerSlices witnessGraph witnessDealer witnessPlayers p s * v s) = ψ p
    simp only [Fin.sum_univ_two, slice_entry, h1, character_add]
    rcases hp with hp | hp
    · have ha := same_parity ψ hψ p p0 (hp.trans hp0.symm)
      change _ * ψ p = a at ha
      simp only [v, ite_eq_left rfl, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      rw [← ha, hp, show character 0 = 1 from rfl, mul_one]
      linear_combination ψ p * (character_sq (phase (joinDealer p 0)))
    · have hb := same_parity ψ hψ p p1 (hp.trans hp1.symm)
      change _ * ψ p = b at hb
      simp only [v, ite_eq_left rfl, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      rw [← hb, hp, show character 1 = -1 from by change (-1 : ℂ) ^ (1 : ℕ) = -1; rw [pow_one]]
      linear_combination ψ p * (character_sq (phase (joinDealer p 0)))

private theorem dealerMarginal :
    (fun s t : Fin 2 => ∑ p : WitnessPlayers,
      witnessGraphState (joinDealer p s) * star (witnessGraphState (joinDealer p t))) =
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let V := dealerSlices witnessGraph witnessDealer witnessPlayers
  let d : ℂ := (Real.sqrt 2 : ℝ)
  have hd : star d = d := Complex.conj_ofReal _
  have hd2 : d * d = 2 := by
    change ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  funext s t
  calc
    _ = ∑ p : WitnessPlayers, (star (V p t) * V p s) / 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [graphState_slice, graphState_slice]
      change (V p s / d) * star (V p t / d) = _
      rw [mul_comm (V p s / d), star_div₀, hd, div_mul_div_comm, hd2]
    _ = (∑ p : WitnessPlayers, star (V p t) * V p s) * (2 : ℂ)⁻¹ := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M t s) witness_encoding_isometry
      change (∑ p : WitnessPlayers, star (V p t) * V p s) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) t s at h
      rw [h]
      by_cases hst : s = t
      · subst t
        simp [Matrix.smul_apply, Matrix.one_apply, one_div]
      · simp [Matrix.smul_apply, Matrix.one_apply, hst, Ne.symm hst]

/-- Proposition 8(2–3) for this lift and dealer. The normalized graph state
is fixed by the lift with a one-dimensional fixed space. Its slices yield
an isometry onto the common fixed space of the shortened operators. -/
theorem witness_proposition8 :
    (∀ x y ψ, graphPauli x (graphPauli y ψ) = graphPauli (x + y) ψ) ∧
    (∀ ψ, (∀ x, graphPauli x ψ = ψ) ↔ ∃ a : ℂ, ψ = fun z => a * witnessGraphState z) ∧
    (∀ x ψ p s, x witnessDealer = 0 → dealerParity x = 0 →
      graphPauli x (fun z => ψ (restrictPlayers z)) (joinDealer p s) = shortenedPauli x ψ p) ∧
    (∀ p s, witnessGraphState (joinDealer p s) =
      dealerSlices witnessGraph witnessDealer witnessPlayers p s / ((Real.sqrt 2 : ℝ) : ℂ)) ∧
    ((fun s t : Fin 2 => ∑ p : WitnessPlayers,
      witnessGraphState (joinDealer p s) * star (witnessGraphState (joinDealer p t))) =
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (dealerSlices witnessGraph witnessDealer witnessPlayers)ᴴ *
      dealerSlices witnessGraph witnessDealer witnessPlayers = 1 ∧
    Set.range (fun v : Fin 2 → ℂ => dealerSlices witnessGraph witnessDealer witnessPlayers *ᵥ v) =
      witnessShortenedCode :=
  ⟨graphPauli_add, graphState_fixed_line, fun x ψ p s _ hz =>
    shortenedPauli_factor x ψ hz p s, graphState_slice, dealerMarginal, witness_encoding_isometry, code_image⟩

#print axioms witness_proposition8

end D5.S3.Quantum.Information.GangulyCircuitAccess
