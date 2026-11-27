/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNonsplitActionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNonsplitActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic elements lift through the charge kernel of an actual P48q subgroup action. -/

import D5.S3.FiniteGroups.Cyclic.CubicLiftKernelInversion
import D5.S3.FiniteGroups.Cyclic.SL47OrderThreeConjugacy
import D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import D5.S3.VertexAlgebra.LatticeInvolution
import OmegaBuild.Commands

/-!
An element acting by charge negation inverts the character diagonals in the
charge kernel. In the exhaustive integral realization of `SL₂(F₄₇)` on P48q,
negation is the unique involution, so it belongs to every even projected
subgroup. The abelian-kernel cubic lift then applies to the actual action.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNonsplitActionObstruction

open LatticeGeneratingFieldLocality (LatticeData Charge Carrier bilinear)
open DiagonalCharacterConjugacy (Character PreservesModes diagonal diagonal_modes diagonal_single
  eq_of_ground ground)
open P48qTwistedChargeAction (lattice)
open ExtremalC48 (SL47)

open private ground_ratio_character from
  D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy

noncomputable section

local notation "ofAdd" => Multiplicative.ofAdd

private theorem exists_orderThree_lift_of_ground_negation
    (D : LatticeData) {E Q : Type*} [Group E] [Group Q]
    (realization : Additive Q →+ AddAut (Charge D))
    (π : E →* Q) (U : E →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (phase : E → Charge D → ℂˣ)
    (hU : Function.Injective U) (hMode : ∀ e, PreservesModes D (U e))
    (hGround : ∀ e a, U e (ground D a) =
      (phase e a : ℂ) • ground D (realization (Additive.ofMul (π e)) a))
    (s x : E) (hs : Commute (π s) (π x))
    (hNeg : ∀ a, realization (Additive.ofMul (π s)) a = -a)
    (hx : orderOf (π x) = 3) :
    ∃ z : E, π z = π x ∧ orderOf z = 3 := by
  have hDiagonal (k : E) (hk : k ∈ π.ker) : ∃ χ : Character D, U k = diagonal D χ := by
    have hFix (a : Charge D) : U k (ground D a) = (phase k a : ℂ) • ground D a := by
      rw [hGround, MonoidHom.mem_ker.mp hk]
      change (phase k a : ℂ) • ground D (realization 0 a) = _
      rw [map_zero]
      rfl
    obtain ⟨χ, hχ⟩ := ground_ratio_character D (U k) (hMode k) (phase k) hFix
    refine ⟨χ, eq_of_ground D (hMode k) (diagonal_modes D χ) fun a => ?_⟩
    rw [hFix, diagonal_single, hχ]
  refine CubicLiftKernelInversion.exists_orderThree_lift π s x ?_ hs ?_ hx
  · intro k l hk hl
    obtain ⟨χ, hχ⟩ := hDiagonal k hk
    obtain ⟨η, hη⟩ := hDiagonal l hl
    change k * l = l * k
    apply hU
    rw [map_mul, map_mul, hχ, hη]
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro a p
    change diagonal D χ (diagonal D η (Finsupp.single a p)) =
      diagonal D η (diagonal D χ (Finsupp.single a p))
    simp only [diagonal_single, map_smul, smul_smul]
    rw [mul_comm (χ (ofAdd a) : ℂ)]
  · intro k hk
    obtain ⟨χ, hχ⟩ := hDiagonal k hk
    have hReflect (a : Charge D) :
        U s (ground D a) = (phase s a : ℂ) • ground D (-a) := by
      rw [hGround, hNeg]
    have hCancel : k * (s * k) = s := by
      apply hU
      apply eq_of_ground D (hMode _) (hMode _)
      intro a
      have hχNeg : χ (ofAdd (-a)) = (χ (ofAdd a))⁻¹ := χ.map_inv (ofAdd a)
      have hScalar : χ (ofAdd a) * (phase s a * χ (ofAdd (-a))) = phase s a := by
        rw [hχNeg, mul_left_comm, mul_inv_cancel, mul_one]
      simp only [map_mul, LinearEquiv.mul_apply, hχ, diagonal_single, map_smul, hReflect,
        smul_smul, ← Units.val_mul, mul_assoc, hScalar]
    calc
      s * k * s⁻¹ = k⁻¹ * (k * (s * k)) * s⁻¹ := by
        rw [← mul_assoc k⁻¹ k, inv_mul_cancel, one_mul]
      _ = k⁻¹ := by rw [hCancel, mul_assoc, mul_inv_cancel, mul_one]

private theorem sl47_orderTwo_eq_neg_one (A : SL47) (hA : orderOf A = 2) :
    A = -(1 : SL47) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hA
  have hinv : A⁻¹ = A := by
    calc
      A⁻¹ = A⁻¹ * (A * A) := by rw [← pow_two, hsq, mul_one]
      _ = A := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hEntries : !![A 1 1, -A 0 1; -A 1 0, A 0 0] =
      (A : Matrix (Fin 2) (Fin 2) (ZMod 47)) := by
    rw [← Matrix.adjugate_fin_two, ← Matrix.SpecialLinearGroup.coe_inv, hinv]
  have h00 : A 1 1 = A 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 47) => M 0 0) hEntries
  have eq_zero_of_neg_eq (a : ZMod 47) (ha : -a = a) : a = 0 := by
    have h : (2 : ZMod 47) * a = 0 := calc
      2 * a = a + a := two_mul a
      _ = -a + a := congrArg (· + a) ha.symm
      _ = 0 := neg_add_cancel a
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  have h01 : A 0 1 = 0 := eq_zero_of_neg_eq _
    (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 47) => M 0 1) hEntries)
  have h10 : A 1 0 = 0 := eq_zero_of_neg_eq _
    (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 47) => M 1 0) hEntries)
  have hd : A 0 0 ^ 2 = 1 := by
    simpa only [Matrix.det_fin_two, h00, h01, h10, zero_mul, sub_zero, pow_two]
      using A.property
  have hScalar (d : ZMod 47) (he : A 0 0 = d) :
      (A : Matrix (Fin 2) (Fin 2) (ZMod 47)) = d • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul, h00, h01, h10, he]
  rcases sq_eq_one_iff.mp hd with he | he
  · exact (hne (Subtype.ext (by simpa using hScalar 1 he))).elim
  · apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_smul,
      one_smul] using hScalar (-1) he

private theorem p48q_neg_one_charge
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    (a : Charge lattice) : realization (Additive.ofMul (-(1 : SL47))) a = -a := by
  let negation : AddAut (Charge lattice) :=
    { toFun := fun b => -b
      invFun := fun b => -b
      left_inv := neg_neg
      right_inv := neg_neg
      map_add' := neg_add }
  obtain ⟨k, hk⟩ := hExhaustive negation (LatticeInvolution.bilinear_neg_neg lattice)
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hOrder : addOrderOf negation = 2 := by
    apply addOrderOf_eq_prime
    · rw [two_nsmul]
      apply AddEquiv.ext
      intro b
      change -(-b) = b
      exact neg_neg b
    · intro he
      have h := DFunLike.congr_fun he (fun _ => 1 : Charge lattice)
      let i : Fin lattice.rank := ⟨0, by change 0 < 48; decide⟩
      have h0 := congrFun h i
      change (-1 : ℤ) = 1 at h0
      omega
  let chargeAction := realization.toMultiplicativeRight
  have hOrderK : orderOf k.toMul = 2 := by
    rw [← orderOf_injective chargeAction (Multiplicative.ofAdd.injective.comp hFaithful) k.toMul]
    change addOrderOf (realization k) = 2
    rwa [hk]
  have hNegK := sl47_orderTwo_eq_neg_one k.toMul hOrderK
  rw [← hNegK]
  change realization k a = -a
  exact DFunLike.congr_fun hk a

/-- For a faithful compatible P48q action whose projected subgroup contains
negation, every specified order-three image element has an actual lift of
order three. Its induced action on the charges also has exact order three. -/
theorem p48q_orderThree_lift_of_neg_one_mem_range
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    {E : Type*} [Group E]
    (π : E →* SL47) (U : E →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice))
    (phase : E → Charge lattice → ℂˣ)
    (hU : Function.Injective U) (hMode : ∀ e, PreservesModes lattice (U e))
    (hGround : ∀ e a, U e (ground lattice a) =
      (phase e a : ℂ) • ground lattice (realization (Additive.ofMul (π e)) a))
    (hNeg : -(1 : SL47) ∈ π.range)
    (x : SL47) (hx : x ∈ π.range) (hxOrder : orderOf x = 3) :
    ∃ z : E, π z = x ∧ orderOf z = 3 ∧
      addOrderOf (realization (Additive.ofMul (π z))) = 3 := by
  obtain ⟨s, hs⟩ := hNeg
  obtain ⟨y, hy⟩ := hx
  have hComm : Commute (π s) (π y) := by
    rw [hs]
    change (-(1 : SL47)) * π y = π y * (-(1 : SL47))
    rw [neg_mul, mul_neg, one_mul, mul_one]
  obtain ⟨z, hz, hzOrder⟩ := exists_orderThree_lift_of_ground_negation lattice
    realization π U phase hU hMode hGround s y hComm
    (fun a => by rw [hs, p48q_neg_one_charge realization hFaithful hExhaustive])
    (hy.symm ▸ hxOrder)
  have hProj : π z = x := hz.trans hy
  let chargeAction := realization.toMultiplicativeRight
  exact ⟨z, hProj, hzOrder,
    (orderOf_injective chargeAction (Multiplicative.ofAdd.injective.comp hFaithful) (π z)).trans
      (hProj.symm ▸ hxOrder)⟩

/-- Cauchy's theorem supplies negation and an order-three image element when
the projected subgroup of a faithful compatible P48q action has order
divisible by both two and three. -/
theorem p48q_orderThree_lift_of_even_range
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    {E : Type*} [Group E]
    (π : E →* SL47) (U : E →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice))
    (phase : E → Charge lattice → ℂˣ)
    (hU : Function.Injective U) (hMode : ∀ e, PreservesModes lattice (U e))
    (hGround : ∀ e a, U e (ground lattice a) =
      (phase e a : ℂ) • ground lattice (realization (Additive.ofMul (π e)) a))
    (hEven : 2 ∣ Nat.card π.range) (hThree : 3 ∣ Nat.card π.range) :
    ∃ z : E, orderOf z = 3 ∧ addOrderOf (realization (Additive.ofMul (π z))) = 3 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := π.range) 2 hEven
  have hsOrder : orderOf (s : SL47) = 2 :=
    (orderOf_injective π.range.subtype Subtype.val_injective s).trans hs
  have hNeg : -(1 : SL47) ∈ π.range := sl47_orderTwo_eq_neg_one s hsOrder ▸ s.property
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π.range) 3 hThree
  have hxOrder : orderOf (x : SL47) = 3 :=
    (orderOf_injective π.range.subtype Subtype.val_injective x).trans hx
  obtain ⟨z, _, hzOrder, hzCharge⟩ := p48q_orderThree_lift_of_neg_one_mem_range
    realization hFaithful hExhaustive π U phase hU hMode hGround hNeg x x.property hxOrder
  exact ⟨z, hzOrder, hzCharge⟩

run_cmd do
  for name in [``p48q_orderThree_lift_of_neg_one_mem_range, ``p48q_orderThree_lift_of_even_range] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNonsplitActionObstruction
