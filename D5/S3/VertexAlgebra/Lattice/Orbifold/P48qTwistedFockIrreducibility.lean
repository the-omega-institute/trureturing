import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
import Mathlib.Data.Finset.Lattice.Fold
import Batteries.Tactic.OpenPrivate

/-!
Irreducibility of the P48q twisted state for the restricted Heisenberg and
charge action of Bakalov–Kac, arXiv:math/0402315v3, Proposition 4.2.
The signed cover index of a current is three times its physical frequency.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFockIrreducibility

open LatticeGeneratingFieldLocality (Charge)
open P48qMomentumEnergy (Fixed fixedGram fixedGram_nondegenerate physicalMomentum)
open P48qTwistedChargeAction (Momentum lattice g U)
open P48qThirdTwistedField (Cartan Fock Mode State creator annihilatorDual fixedDualBases
  pair_modes chargePhase chargePhase_ne_zero U_ground shift_numerator fieldCoeff
  momentumExponent concreteChargedField concreteChargedField_ground_leading chargedField_coeff)
open P48qTwistedHeisenberg (mode scale annCoordinates creCoordinates mode_zero_apply
  mode_positive_apply mode_negative_apply)
open D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.API (totalDegree_pderiv_lt)
open MvPolynomial
open scoped BigOperators TensorProduct

open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

noncomputable section

local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "N" => ThirdTwistedChargeAction.N lattice g

theorem physicalMomentum_injective : Function.Injective physicalMomentum := by
  intro p q hpq
  apply Subtype.ext
  funext i
  have hi := congrArg (fun x : Fixed => (x : Cartan) i) hpq
  change (3 : ℂ)⁻¹ • (p.1 i : ℂ) = (3 : ℂ)⁻¹ • (q.1 i : ℂ) at hi
  simp only [smul_eq_mul] at hi
  have hcast := mul_left_cancel₀ (inv_ne_zero (by norm_num : (3 : ℂ) ≠ 0)) hi
  exact_mod_cast hcast

theorem fixedCartan_separates {p q : Momentum} (hpq : p ≠ q) :
    ∃ h : Fixed, fixedGram h (physicalMomentum p) ≠ fixedGram h (physicalMomentum q) := by
  by_contra! hall
  apply hpq
  apply physicalMomentum_injective
  apply sub_eq_zero.mp
  apply fixedGram_nondegenerate.2
  intro h
  rw [LinearMap.BilinForm.sub_right, hall h, sub_self]

private theorem mode_fixed_zero_apply (h : Fixed) (v : State) (p : Momentum) :
    mode (h : Cartan) 0 v p = fixedGram h (physicalMomentum p) • v p :=
  mode_zero_apply (h : Cartan) v p

/-- A finite product of shifted Cartan zero modes recovers each momentum
component of a vector in an invariant submodule. Each factor can use its own
fixed direction. -/
theorem momentum_component_mem (S : Submodule ℂ State)
    (hzero : ∀ (h : Fixed) (v : State), v ∈ S → mode (h : Cartan) 0 v ∈ S)
    {w : State} (hw : w ∈ S) (p : Momentum) :
    Finsupp.single p (w p) ∈ S := by
  classical
  have eliminate (s : Finset Momentum) (hp : p ∉ s) :
      ∃ v : State, ∃ c : ℂ, v ∈ S ∧ c ≠ 0 ∧ v p = c • w p ∧
        ∀ r, r ∈ s ∨ w r = 0 → v r = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨w, 1, hw, one_ne_zero, (one_smul ℂ (w p)).symm, by simp⟩
    | @insert q s _ ih =>
      have hpq : p ≠ q := fun he => hp (Finset.mem_insert.mpr (Or.inl he))
      have hps : p ∉ s := fun hs => hp (Finset.mem_insert.mpr (Or.inr hs))
      obtain ⟨v, c, hv, hc, hvp, hvzero⟩ := ih hps
      obtain ⟨h, hsep⟩ := fixedCartan_separates hpq
      let value : Momentum → ℂ := fun r => fixedGram h (physicalMomentum r)
      let y : State := mode (h : Cartan) 0 v - value q • v
      have hy (r : Momentum) : y r = (value r - value q) • v r := by
        simp only [y, Finsupp.sub_apply, Finsupp.smul_apply, mode_fixed_zero_apply,
          value, sub_smul]
      refine ⟨y, (value p - value q) * c, S.sub_mem (hzero h v hv) (S.smul_mem _ hv),
        mul_ne_zero (sub_ne_zero.mpr hsep) hc, ?_, ?_⟩
      · rw [hy, hvp, smul_smul]
      · intro r hr
        rw [hy]
        rcases hr with hr | hr
        · rcases Finset.mem_insert.mp hr with rfl | hrs
          · rw [sub_self, zero_smul]
          · rw [hvzero r (Or.inl hrs), smul_zero]
        · rw [hvzero r (Or.inr hr), smul_zero]
  obtain ⟨v, c, hv, hc, hvp, hvzero⟩ :=
    eliminate (w.support.erase p) (Finset.notMem_erase p w.support)
  have hvSingle : v = c • Finsupp.single p (w p) := by
    apply Finsupp.ext
    intro r
    by_cases hrp : r = p
    · subst r
      simpa only [Finsupp.smul_apply, Finsupp.single_eq_same] using hvp
    · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hrp, smul_zero]
      apply hvzero r
      by_cases hr : r ∈ w.support
      · exact Or.inl (Finset.mem_erase.mpr ⟨hrp, hr⟩)
      · exact Or.inr (Finsupp.notMem_support_iff.mp hr)
  have recovered := S.smul_mem c⁻¹ hv
  simpa only [hvSingle, smul_smul, inv_mul_cancel₀ hc, one_smul] using recovered

/-- The actual negative mode of a basis creator is coordinate multiplication. -/
theorem negative_mode_coordinate (i : Fin 16) (n : ℕ) (v : State) (p : Momentum) :
    mode (creator fixedDualBases (i, n)) (.negSucc n) v p = X (i, n) * v p := by
  classical
  rw [mode_negative_apply]
  simp only [creCoordinates, pair_modes, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- The actual positive mode in the Gram-dual direction is the coordinate
derivative times its physical frequency. -/
theorem positive_mode_coordinate (i : Fin 16) (n : ℕ) (v : State) (p : Momentum) :
    mode (annihilatorDual fixedDualBases (i, n)) (.ofNat (n + 1)) v p =
      scale n • pderiv (i, n) (v p) := by
  classical
  have h (j : Fin 16) :
      annCoordinates (annihilatorDual fixedDualBases (i, n)) n j =
        if j = i then 1 else 0 := by
    exact (formSymmetric.eq _ _).trans (pair_modes fixedDualBases j i n)
  rw [mode_positive_apply]
  simp only [h, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem negative_mode_single (i : Fin 16) (n : ℕ) (p : Momentum) (P : Fock) :
    mode (creator fixedDualBases (i, n)) (.negSucc n) (Finsupp.single p P) =
      Finsupp.single p (X (i, n) * P) := by
  apply Finsupp.ext
  intro q
  rw [negative_mode_coordinate]
  by_cases h : q = p
  · subst q
    simp only [Finsupp.single_eq_same]
  · simp only [Finsupp.single_eq_of_ne h, mul_zero]

theorem positive_mode_single (i : Fin 16) (n : ℕ) (p : Momentum) (P : Fock) :
    mode (annihilatorDual fixedDualBases (i, n)) (.ofNat (n + 1)) (Finsupp.single p P) =
      scale n • Finsupp.single p (pderiv (i, n) P) := by
  apply Finsupp.ext
  intro q
  rw [positive_mode_coordinate, Finsupp.smul_apply]
  by_cases h : q = p
  · subst q
    simp only [Finsupp.single_eq_same]
  · simp only [Finsupp.single_eq_of_ne h, map_zero]

private theorem scale_ne_zero (n : ℕ) : scale n ≠ 0 := by
  unfold scale
  exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (by norm_num)

/-- Apply coordinate partial derivatives in the given order. -/
def applyPartials : List Mode → Fock → Fock
  | [], P => P
  | i :: word, P => applyPartials word (pderiv i P)

/-- Differentiating along a maximal-total-degree monomial gives a nonzero
constant in exactly as many partial derivatives as the total degree. -/
theorem exists_constant_derivative_word (P : Fock) (hP : P ≠ 0) :
    ∃ word : List Mode, word.length = P.totalDegree ∧
      ∃ c : ℂ, c ≠ 0 ∧ applyPartials word P = C c := by
  classical
  have extract (n : ℕ) : ∀ Q : Fock, Q.totalDegree = n → Q ≠ 0 →
      ∃ word : List Mode, word.length = Q.totalDegree ∧
        ∃ c : ℂ, c ≠ 0 ∧ applyPartials word Q = C c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hdeg hQ
      by_cases hzero : Q.totalDegree = 0
      · have hC := totalDegree_eq_zero_iff_eq_C.mp hzero
        have hc : Q.coeff 0 ≠ 0 := by
          intro hc
          exact hQ (by rw [hC, hc, C_0])
        exact ⟨[], hzero.symm, Q.coeff 0, hc, hC⟩
      · obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup Q.support
          (MvPolynomial.support_nonempty.mpr hQ)
          (fun d : Mode →₀ ℕ => d.sum fun _ e => e)
        change Q.totalDegree = d.sum (fun _ e => e) at hmax
        have hd0 : d ≠ 0 := by
          intro hz
          exact hzero (by simpa [hz] using hmax)
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
        let e := d - Finsupp.single i 1
        have hsplit : e + Finsupp.single i 1 = d :=
          Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)
        have hcoeff : (pderiv i Q).coeff e ≠ 0 := by
          rw [coeff_pderiv, hsplit]
          have hscalar : (e i : ℂ) + 1 ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero (e i)
          exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hscalar
        have hderiv : pderiv i Q ≠ 0 := by
          intro hz
          exact hcoeff (by rw [hz]; rfl)
        have hlt := totalDegree_pderiv_lt Q i hderiv
        have hle : e.sum (fun _ m => m) ≤ (pderiv i Q).totalDegree :=
          le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
        have hsum : d.sum (fun _ m => m) = e.sum (fun _ m => m) + 1 := by
          calc
            d.sum (fun _ m => m) = (e + Finsupp.single i 1).sum (fun _ m => m) := by
              rw [hsplit]
            _ = _ := by simp [Finsupp.sum_add_index']
        obtain ⟨word, hlength, c, hc, hword⟩ :=
          ih (pderiv i Q).totalDegree (hdeg ▸ hlt) (pderiv i Q) rfl hderiv
        refine ⟨i :: word, ?_, c, hc, hword⟩
        rw [List.length_cons, hlength]
        omega
  exact extract P.totalDegree P rfl hP

/-- A nonzero polynomial in an isolated momentum summand yields that
summand's Fock vacuum under positive modes and scalar multiplication. -/
theorem ground_mem_of_single_mem (S : Submodule ℂ State)
    (hmode : ∀ (u : Cartan) (k : ℤ) (v : State), v ∈ S → mode u k v ∈ S)
    {p : Momentum} {P : Fock} (hP : P ≠ 0) (hp : Finsupp.single p P ∈ S) :
    Finsupp.single p (1 : Fock) ∈ S := by
  have step (j : Mode) (Q : Fock) (hQ : Finsupp.single p Q ∈ S) :
      Finsupp.single p (pderiv j Q) ∈ S := by
    rcases j with ⟨i, n⟩
    have h := hmode (annihilatorDual fixedDualBases (i, n))
      (.ofNat (n + 1)) (Finsupp.single p Q) hQ
    rw [positive_mode_single] at h
    have normalized := S.smul_mem (scale n)⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ (scale_ne_zero n), one_smul] using normalized
  have word_mem (word : List Mode) : ∀ Q : Fock, Finsupp.single p Q ∈ S →
      Finsupp.single p (applyPartials word Q) ∈ S := by
    induction word with
    | nil => exact fun _ hQ => hQ
    | cons j word ih => exact fun Q hQ => ih _ (step j Q hQ)
  obtain ⟨word, _, c, hc, hword⟩ := exists_constant_derivative_word P hP
  have h := word_mem word P hp
  rw [hword] at h
  have hC : c • (1 : Fock) = C c := by rw [smul_eq_C_mul, mul_one]
  have recovered := S.smul_mem c⁻¹ h
  simpa only [← hC, ← Finsupp.smul_single, smul_smul, inv_mul_cancel₀ hc, one_smul]
    using recovered

/-- Negative modes generate the entire polynomial summand from its vacuum. -/
theorem single_mem_of_ground_mem (S : Submodule ℂ State)
    (hmode : ∀ (u : Cartan) (k : ℤ) (v : State), v ∈ S → mode u k v ∈ S)
    {p : Momentum} (hp : Finsupp.single p (1 : Fock) ∈ S) (P : Fock) :
    Finsupp.single p P ∈ S := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [Finsupp.smul_single, smul_eq_C_mul, mul_one] using S.smul_mem c hp
  | add P Q hP hQ =>
    rw [Finsupp.single_add]
    exact S.add_mem hP hQ
  | mul_X P j hP =>
    rcases j with ⟨i, n⟩
    have h := hmode (creator fixedDualBases (i, n)) (.negSucc n) (Finsupp.single p P) hP
    simpa only [negative_mode_single, mul_comm (X (i, n)) P] using h

theorem charge_shift_transitive (p q : Momentum) : ∃ a : Charge lattice, shift a p = q := by
  obtain ⟨a, ha⟩ := (show ∃ a : Charge lattice, N a = (q - p).1 from (q - p).2)
  refine ⟨a, Subtype.ext ?_⟩
  rw [shift_numerator, ha]
  change p.1 + (q.1 - p.1) = q.1
  abel

/-- The existing ground charge operator extended by the identity on Fock. -/
def chargeOperator (a : Charge lattice) : Module.End ℂ State :=
  (TensorProduct.finsuppScalarLeft ℂ Fock Momentum).conj ((U a).rTensor Fock)

theorem chargeOperator_single (a : Charge lattice) (p : Momentum) (P : Fock) :
    chargeOperator a (Finsupp.single p P) =
      Finsupp.single (shift a p) (chargePhase a p • P) := by
  rw [chargeOperator, LinearEquiv.conj_apply_apply,
    TensorProduct.finsuppScalarLeft_symm_apply_single, LinearMap.rTensor_tmul, U_ground]
  apply Finsupp.ext
  intro q
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  by_cases h : q = shift a p
  · subst q
    simp only [Finsupp.single_eq_same]
  · have hphase : (Finsupp.single (shift a p) (chargePhase a p) : Momentum →₀ ℂ) q = 0 :=
      Finsupp.single_eq_of_ne h
    rw [hphase, Finsupp.single_eq_of_ne h, zero_smul]

/-- On the restricted current action it suffices to have charge transport on
the Fock vacua, with the phases of the concrete ground operators. -/
theorem irreducible_of_ground_shifts (S : Submodule ℂ State)
    (hmode : ∀ (u : Cartan) (k : ℤ) (v : State), v ∈ S → mode u k v ∈ S)
    (hground : ∀ (a : Charge lattice) (p : Momentum), Finsupp.single p (1 : Fock) ∈ S →
      Finsupp.single (shift a p) (chargePhase a p • (1 : Fock)) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := S.ne_bot_iff.mp hbot
  obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hw0
  have hsingle := momentum_component_mem S (fun h v hv => hmode (h : Cartan) 0 v hv) hw p
  have hpGround := ground_mem_of_single_mem S hmode (Finsupp.mem_support_iff.mp hp) hsingle
  have allGround (q : Momentum) : Finsupp.single q (1 : Fock) ∈ S := by
    obtain ⟨a, ha⟩ := charge_shift_transitive p q
    have h := hground a p hpGround
    rw [ha, ← Finsupp.smul_single] at h
    have recovered := S.smul_mem (chargePhase a p)⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ (chargePhase_ne_zero a p), one_smul] using recovered
  apply top_unique
  intro v _
  rw [← Finsupp.sum_single v]
  change (∑ q ∈ v.support, Finsupp.single q (v q)) ∈ S
  exact S.sum_mem fun q _ => single_mem_of_ground_mem S hmode (allGround q) (v q)

/-- The actual restricted P48q Heisenberg and charge action is irreducible. -/
theorem restricted_pair_irreducible (S : Submodule ℂ State)
    (hmode : ∀ (u : Cartan) (k : ℤ) (v : State), v ∈ S → mode u k v ∈ S)
    (hcharge : ∀ (a : Charge lattice) (v : State), v ∈ S → chargeOperator a v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  apply irreducible_of_ground_shifts S hmode
  intro a p hp
  rw [← chargeOperator_single]
  exact hcharge a _ hp

/-- The actual charged-field coefficients also suffice for the charge step.
At a pure ground vector the leading coefficient is the same phase shift. -/
theorem current_charged_coeff_irreducible (S : Submodule ℂ State)
    (hmode : ∀ (u : Cartan) (k : ℤ) (v : State), v ∈ S → mode u k v ∈ S)
    (hcharge : ∀ (a : Charge lattice) (k : ℤ) (v : State),
      v ∈ S → fieldCoeff fixedDualBases a k v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  apply irreducible_of_ground_shifts S hmode
  intro a p hp
  have hlead := concreteChargedField_ground_leading a p
  rw [concreteChargedField, chargedField_coeff] at hlead
  rw [← hlead]
  exact hcharge a (momentumExponent a p) _ hp

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFockIrreducibility
