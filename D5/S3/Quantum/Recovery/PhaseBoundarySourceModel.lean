/- GID: D5/S3/Quantum/Recovery/PhaseBoundarySourceModel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundarySourceModel
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Actual flagged source and coherent target with inaccessible memory. -/

import D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import Mathlib.Tactic

noncomputable section

universe u

namespace D5.S3.Quantum.Recovery.PhaseBoundarySourceModel

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

abbrev Qubit := Fin 2

/-- The source memory is the first qubit; only the second is received. -/
def xi (ell : ℝ) : Qubit × Qubit → ℂ := fun p =>
  if p = (0, 0) then (Real.sqrt (1 - ell) : ℂ)
  else if p = (1, 1) then (Real.sqrt ell : ℂ) else 0

/-- The Pauli Y action is on the received qubit alone. -/
def psi (ell : ℝ) : Qubit × Qubit → ℂ := fun p =>
  if p = (0, 1) then Complex.I * (Real.sqrt (1 - ell) : ℂ)
  else if p = (1, 0) then -Complex.I * (Real.sqrt ell : ℂ) else 0

private theorem psi_pauli (ell : ℝ) :
    psi ell = ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ
      (!![0, -Complex.I; Complex.I, 0] : Matrix Qubit Qubit ℂ)) *ᵥ xi ell := by
  funext ⟨m, a⟩
  fin_cases m <;> fin_cases a <;>
    simp [psi, xi, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

def outer {A : Type*} (u v : A → ℂ) : Matrix A A ℂ :=
  Matrix.vecMulVec u (star v)

/-- The flag value 0 denotes +1, and 1 denotes -1. -/
def flagSign (s : Qubit) : ℝ := if s = 0 then 1 else -1

def eta (ell beta gamma w : ℝ) (s : Qubit) :
    Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  ((1 - beta * w : ℝ) : ℂ) • outer (xi ell) (xi ell) +
    ((beta * w : ℝ) : ℂ) • outer (psi ell) (psi ell) +
    ((flagSign s * gamma * w : ℝ) : ℂ) •
      (outer (xi ell) (psi ell) + outer (psi ell) (xi ell))

private theorem sqrt_square {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t : ℂ)^2 = (t : ℂ) := by
  exact_mod_cast Real.sq_sqrt ht

private theorem xi_norm {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) :
    star (xi ell) ⬝ᵥ xi ell = 1 := by
  have hr := sqrt_square (sub_nonneg.mpr hu)
  have he := sqrt_square hl
  simp [xi, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← pow_two, hr, he]

private theorem psi_norm {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) :
    star (psi ell) ⬝ᵥ psi ell = 1 := by
  have hr := sqrt_square (sub_nonneg.mpr hu)
  have he := sqrt_square hl
  simp [psi, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  calc
    _ = (Real.sqrt (1 - ell) : ℂ)^2 + (Real.sqrt ell : ℂ)^2 := by
      ring_nf
      simp [Complex.I_sq]
    _ = 1 := by rw [hr, he]; push_cast; ring

private theorem xi_psi_orthogonal (ell : ℝ) :
    star (xi ell) ⬝ᵥ psi ell = 0 ∧ star (psi ell) ⬝ᵥ xi ell = 0 := by
  simp [xi, psi, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem eta_trace {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1)
    (beta gamma w : ℝ) (s : Qubit) : Matrix.trace (eta ell beta gamma w s) = 1 := by
  simp only [eta, Matrix.trace_add, Matrix.trace_smul, outer, Matrix.trace_vecMulVec]
  rw [dotProduct_comm (xi ell), dotProduct_comm (psi ell),
    dotProduct_comm (xi ell), dotProduct_comm (psi ell),
    xi_norm hl hu, psi_norm hl hu, (xi_psi_orthogonal ell).1,
    (xi_psi_orthogonal ell).2]
  push_cast
  ring

private theorem eta_positive {ell beta gamma w : ℝ} (hb : 0 < beta)
    (hw : 0 ≤ w) (hmax : w ≤ beta / (beta ^ 2 + gamma ^ 2)) (s : Qubit) :
    (eta ell beta gamma w s).PosSemidef := by
  have hk : 0 < beta ^ 2 + gamma ^ 2 := by positivity
  have hbudget : (beta ^ 2 + gamma ^ 2)*w ≤ beta := by
    nlinarith [(le_div_iff₀ hk).mp hmax]
  have hd : 0 ≤ 1 - (beta ^ 2 + gamma ^ 2) * w / beta := by
    exact sub_nonneg.mpr ((div_le_one hb).mpr hbudget)
  let v := fun p => (flagSign s * gamma : ℂ) * xi ell p + (beta : ℂ) * psi ell p
  have hsign : flagSign s ^ 2 = 1 := by
    fin_cases s <;> norm_num [flagSign]
  have hdecomp : eta ell beta gamma w s =
      ((1 - (beta ^ 2 + gamma ^ 2) * w / beta : ℝ) : ℂ) • outer (xi ell) (xi ell) +
      ((w / beta : ℝ) : ℂ) • outer v v := by
    ext p q
    simp [eta, outer, Matrix.vecMulVec_apply, v, Matrix.smul_apply,
      Pi.star_apply, star_add, star_mul]
    have hbC : (beta : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hsC : (flagSign s : ℂ)^2 = 1 := by exact_mod_cast hsign
    field_simp
    ring_nf
    simp [hsC]
  rw [hdecomp]
  exact ((Matrix.posSemidef_vecMulVec_self_star (xi ell)).smul
    (show (0 : ℂ) ≤ ((1 - (beta ^ 2 + gamma ^ 2) * w / beta : ℝ) : ℂ) by exact_mod_cast hd)).add
    ((Matrix.posSemidef_vecMulVec_self_star v).smul
      (show (0 : ℂ) ≤ ((w / beta : ℝ) : ℂ) by exact_mod_cast div_nonneg hw hb.le))

/-- Register order is M × (actual flag × received qubit). -/
def omega (ell beta gamma w : ℝ) :
    Matrix (Qubit × (Qubit × Qubit)) (Qubit × (Qubit × Qubit)) ℂ :=
  fun p q => if p.2.1 = q.2.1 then
    (1/2 : ℂ) * eta ell beta gamma w p.2.1 (p.1, p.2.2) (q.1, q.2.2) else 0

private theorem omega_positive {ell beta gamma w : ℝ} (hb : 0 < beta)
    (hw : 0 ≤ w) (hmax : w ≤ beta / (beta ^ 2 + gamma ^ 2)) :
    (omega ell beta gamma w).PosSemidef := by
  let block (s : Qubit) :
      Matrix (Qubit × (Qubit × Qubit)) (Qubit × (Qubit × Qubit)) ℂ :=
    fun p q => if p.2.1 = s ∧ q.2.1 = s then
      eta ell beta gamma w s (p.1, p.2.2) (q.1, q.2.2) else 0
  have hblock (s : Qubit) : (block s).PosSemidef := by
    have hpos : 0 ≤ insertBlock s (CStarMatrix.ofMatrix (eta ell beta gamma w s)) :=
      map_nonneg (insertBlock s) (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (eta_positive hb hw hmax s).nonneg)
    have hmat := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hpos)
    exact hmat.submatrix (fun p : Qubit × (Qubit × Qubit) => (p.2.1, (p.1, p.2.2)))
  have heq : omega ell beta gamma w = (1/2 : ℂ) • (block 0 + block 1) := by
    ext ⟨m, s, a⟩ ⟨n, t, b⟩
    fin_cases s <;> fin_cases t <;>
      simp [omega, block, Matrix.smul_apply]
  rw [heq]
  exact ((hblock 0).add (hblock 1)).smul
    (show (0 : ℂ) ≤ (1/2 : ℂ) by exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)

private theorem omega_trace {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1)
    (beta gamma w : ℝ) : Matrix.trace (omega ell beta gamma w) = 1 := by
  have he (s : Qubit) := eta_trace hl hu beta gamma w s
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, omega, ite_true]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he' (s : Qubit) : (∑ m, ∑ a, eta ell beta gamma w s (m, a) (m, a)) = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type] using he s
  simp_rw [he']
  norm_num [Fin.sum_univ_two]

private theorem prepare_channel {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : A → DensityState B) :
    ∃ N : QuantumChannel A B, ∀ X : Matrix A A ℂ,
      CStarMatrix.ofMatrix.symm (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ j, X j j • CStarMatrix.ofMatrix.symm (rho j).1 := by
  classical
  have hf (j : A) : ∃ L : Matrix B B ℂ,
      L * L.conjTranspose = CStarMatrix.ofMatrix.symm (rho j).1 := by
    obtain ⟨T, hT⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (density_posSemidef (rho j)).nonneg
    exact ⟨T.conjTranspose, by
      simpa only [Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose] using hT.symm⟩
  choose L hL using hf
  let K : A × B → Matrix B A ℂ := fun t p j => if j = t.1 then L t.1 p t.2 else 0
  have hK : (∑ t, (K t).conjTranspose * K t) = 1 := by
    ext j l
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    change (∑ t : A × B, ∑ p : B,
      star (if j = t.1 then L t.1 p t.2 else 0) *
        (if l = t.1 then L t.1 p t.2 else 0)) = (1 : Matrix A A ℂ) j l
    rw [Fintype.sum_prod_type]
    by_cases hjl : j = l
    · subst l
      rw [Finset.sum_eq_single j]
      · simp only [if_true]
        change (Matrix.trace ((L j).conjTranspose * L j)) = (1 : Matrix A A ℂ) j j
        rw [Matrix.trace_mul_comm, hL]
        exact (rho j).2.2.trans (by simp)
      · intro i _ hij
        simp [Ne.symm hij]
      · simp
    · have hzero (i : A) (k : B) (p : B) :
          star (if j = i then L i p k else 0) *
            (if l = i then L i p k else 0) = 0 := by
        by_cases hji : j = i <;> by_cases hli : l = i <;> simp_all
      simp only [hzero, Finset.sum_const_zero]
      simp [Matrix.one_apply, hjl]
  obtain ⟨N, hN⟩ := finite_kraus_quantum_channel K hK
  refine ⟨N, fun X => (hN X).trans ?_⟩
  ext p q
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.conjTranspose_apply, K, Matrix.smul_apply, smul_eq_mul]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, apply_ite, star_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ k, L j p k * X j j * star (L j q k)) =
        X j j * (L j * (L j).conjTranspose) p q := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hL]

/-- The actual noisy preparation channel, with M kept outside the receiver. -/
def sourceChannel (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2)) :
    QuantumChannel Qubit (Qubit × (Qubit × Qubit)) :=
  (prepare_channel fun j =>
    ⟨CStarMatrix.ofMatrix (omega ell beta gamma (w j)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (omega_positive hb (hw j) (hmax j)).nonneg,
      omega_trace hl hu beta gamma (w j)⟩).choose

private theorem source_action (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (X : Matrix Qubit Qubit ℂ) :
    CStarMatrix.ofMatrix.symm ((sourceChannel ell beta gamma w hl hu hb hw hmax).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) =
      ∑ j, X j j • omega ell beta gamma (w j) :=
  (prepare_channel _).choose_spec X

private theorem coherent_channel {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) :
    ∃ V : QuantumChannel Qubit (Qubit × (Qubit × Qubit)),
      ∀ (X : Matrix Qubit Qubit ℂ) (p q : Qubit × (Qubit × Qubit)),
        V.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) p q =
          X p.2.1 q.2.1 * xi ell (p.1, p.2.2) * star (xi ell (q.1, q.2.2)) := by
  let K : Matrix (Qubit × (Qubit × Qubit)) Qubit ℂ :=
    fun p j => if p.2.1 = j then xi ell (p.1, p.2.2) else 0
  have hK : (∑ _ : Unit, K.conjTranspose * K) = 1 := by
    simp only [Fintype.sum_unique]
    ext j l
    change (∑ p : Qubit × (Qubit × Qubit),
      star (if p.2.1 = j then xi ell (p.1, p.2.2) else 0) *
        (if p.2.1 = l then xi ell (p.1, p.2.2) else 0)) =
      (1 : Matrix Qubit Qubit ℂ) j l
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    by_cases hjl : j = l
    · subst l
      simp only [apply_ite, star_zero, ite_mul, mul_ite, zero_mul, mul_zero, ite_self,
        ← Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simpa [dotProduct, Fintype.sum_prod_type] using xi_norm hl hu
    · have hzero (m s a : Qubit) :
          star (if s = j then xi ell (m, a) else 0) *
            (if s = l then xi ell (m, a) else 0) = 0 := by
        by_cases hsj : s = j <;> by_cases hsl : s = l <;> simp_all
      simp only [hzero, Finset.sum_const_zero]
      simp [Matrix.one_apply, hjl]
  obtain ⟨V, hV⟩ := finite_kraus_quantum_channel (fun _ : Unit => K) hK
  refine ⟨V, fun X p q => ?_⟩
  have hv := congrFun (congrFun (hV X) p) q
  rcases q with ⟨n, t, b⟩
  fin_cases t <;>
    simpa [K, Fintype.sum_unique, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ite_mul, mul_ite, mul_assoc, mul_comm, mul_left_comm] using hv

/-- The coherent target retains all input off-diagonal entries. -/
def targetChannel (ell : ℝ) (hl : 0 ≤ ell) (hu : ell ≤ 1) :
    QuantumChannel Qubit (Qubit × (Qubit × Qubit)) :=
  (coherent_channel hl hu).choose

private theorem local_channel {M : Type*} {A B : Type u}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (D : QuantumChannel A B) :
    ∃ L : QuantumChannel (M × A) (M × B),
      ∀ (X : CStarMatrix (M × A) (M × A) ℂ) (p q : M × B),
        L.toCompletelyPositiveMap X p q = D.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix fun a b => X (p.1, a) (q.1, b)) p.2 q.2 := by
  classical
  obtain ⟨K, hK, hD⟩ := channel_kraus_stinespring.1 D
  let T : B × A → Matrix (M × B) (M × A) ℂ :=
    fun k p q => if p.1 = q.1 then K k p.2 q.2 else 0
  have hT : (∑ k, (T k).conjTranspose * T k) = 1 := by
    ext ⟨m, a⟩ ⟨n, c⟩
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    change (∑ k : B × A, ∑ p : M × B,
      star (if p.1 = m then K k p.2 a else 0) *
        (if p.1 = n then K k p.2 c else 0)) = (1 : Matrix (M × A) (M × A) ℂ) (m, a) (n, c)
    by_cases hmn : m = n
    · subst n
      have hdiag (k : B × A) :
          (∑ p : M × B, star (if p.1 = m then K k p.2 a else 0) *
            (if p.1 = m then K k p.2 c else 0)) =
            ∑ b, star (K k b a) * K k b c := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
        · simp
        · intro t _ htm
          simp [htm]
        · simp
      simp_rw [hdiag]
      have hh := congrFun (congrFun hK a) c
      simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] using hh
    · have hzero (k : B × A) (p : M × B) :
          star (if p.1 = m then K k p.2 a else 0) *
            (if p.1 = n then K k p.2 c else 0) = 0 := by
        by_cases htm : p.1 = m <;> by_cases htn : p.1 = n <;> simp_all
      simp only [hzero, Finset.sum_const_zero]
      simp [Matrix.one_apply, hmn]
  obtain ⟨L, hL⟩ := finite_kraus_quantum_channel T hT
  refine ⟨L, fun X p q => ?_⟩
  have hh := congrFun (congrFun (hL (CStarMatrix.ofMatrix.symm X)) p) q
  change CStarMatrix.ofMatrix.symm (L.toCompletelyPositiveMap X) p q =
    CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun a b => X (p.1, a) (q.1, b))) p.2 q.2
  rw [hD]
  simpa [T, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, apply_ite] using hh

/-- Identity on the inaccessible memory, tensor an arbitrary receiver channel.
The Kraus realization is obtained from the frozen all-CPTP contract. -/
def receiverChannel {M : Type*} {A B : Type u}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (D : QuantumChannel A B) :
    QuantumChannel (M × A) (M × B) :=
  (local_channel D).choose

def memory (ell : ℝ) : Matrix Qubit Qubit ℂ :=
  Matrix.diagonal ![((1 - ell : ℝ) : ℂ), (ell : ℂ)]

private theorem omega_memory {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1)
    (beta gamma w : ℝ) (m n : Qubit) :
    (∑ s : Qubit, ∑ a : Qubit,
      omega ell beta gamma w (m, (s, a)) (n, (s, a))) = memory ell m n := by
  have hr := sqrt_square (sub_nonneg.mpr hu)
  have he := sqrt_square hl
  fin_cases m <;> fin_cases n <;>
    simp [omega, eta, outer, xi, psi, flagSign, Fin.sum_univ_two, memory,
      Matrix.vecMulVec_apply, Matrix.diagonal] <;>
    ring_nf <;> simp [Complex.I_sq, hr, he]

theorem source_reference {F : Type*} [Fintype F] [DecidableEq F]
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
    (f g : F) (p q : Qubit × (Qubit × Qubit)) :
    referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax) X (f, p) (g, q) =
      ∑ j, X (f, j) (g, j) * omega ell beta gamma (w j) p q := by
  change (sourceChannel ell beta gamma w hl hu hb hw hmax).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix fun j k => X (f, j) (g, k)) p q = _
  have hh := congrFun (congrFun (source_action ell beta gamma w hl hu hb hw hmax
    (fun j k => X (f, j) (g, k))) p) q
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    CStarMatrix.ofMatrix_symm_apply] using hh

theorem target_reference {F : Type*} [Fintype F] [DecidableEq F]
    (ell : ℝ) (hl : 0 ≤ ell) (hu : ell ≤ 1)
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
    (f g : F) (p q : Qubit × (Qubit × Qubit)) :
    referenceAction (targetChannel ell hl hu) X (f, p) (g, q) =
      X (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) * star (xi ell (q.1, q.2.2)) :=
  (coherent_channel hl hu).choose_spec _ p q

theorem receiver_reference {F M : Type*} {A B : Type u}
    [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (D : QuantumChannel A B)
    (X : CStarMatrix (F × (M × A)) (F × (M × A)) ℂ)
    (f g : F) (m n : M) (b c : B) :
    referenceAction (receiverChannel (M := M) D) X (f, (m, b)) (g, (n, c)) =
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun a d => X (f, (m, a)) (g, (n, d))) b c :=
  (local_channel D).choose_spec _ (m, b) (n, c)

private theorem receiver_memory {F M : Type*} {A B : Type u}
    [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (D : QuantumChannel A B)
    (X : CStarMatrix (F × (M × A)) (F × (M × A)) ℂ)
    (f g : F) (m n : M) :
    (∑ b, referenceAction (receiverChannel (M := M) D) X (f, (m, b)) (g, (n, b))) =
      ∑ a, X (f, (m, a)) (g, (n, a)) := by
  simp_rw [receiver_reference]
  exact D.trace_preserving (CStarMatrix.ofMatrix fun a d => X (f, (m, a)) (g, (n, d)))

/-- One physical source/target pair, on the full legal parameter range, has the
actual flagged preparation and coherent target action at every finite reference.
Every CPTP receiver decoder is local to flag/R and preserves the F/M marginal. -/
theorem phase_boundary_source_complete
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2)) :
    (psi ell = ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ
      (!![0, -Complex.I; Complex.I, 0] : Matrix Qubit Qubit ℂ)) *ᵥ xi ell) ∧
    (∀ j s, (eta ell beta gamma (w j) s).PosSemidef ∧
      Matrix.trace (eta ell beta gamma (w j) s) = 1) ∧
    (∀ {F : Type*} [Fintype F] [DecidableEq F]
      (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
      (f g : F) (p q : Qubit × (Qubit × Qubit)),
      referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax) X (f, p) (g, q) =
        ∑ j, X (f, j) (g, j) * omega ell beta gamma (w j) p q) ∧
    (∀ {F : Type*} [Fintype F] [DecidableEq F]
      (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
      (f g : F) (p q : Qubit × (Qubit × Qubit)),
      referenceAction (targetChannel ell hl hu) X (f, p) (g, q) =
        X (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) * star (xi ell (q.1, q.2.2))) ∧
    (∀ {F : Type*} {B : Type} [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]
      (D : QuantumChannel (Qubit × Qubit) B)
      (X : CStarMatrix (F × (Qubit × (Qubit × Qubit)))
        (F × (Qubit × (Qubit × Qubit))) ℂ) (f g : F) (m n : Qubit),
      (∑ b, referenceAction (receiverChannel (M := Qubit) D) X (f, (m, b)) (g, (n, b))) =
        ∑ a, X (f, (m, a)) (g, (n, a))) ∧
    (∀ {F : Type*} {B : Type} [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B]
      (D : QuantumChannel (Qubit × Qubit) B)
      (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
      (f g : F) (m n : Qubit),
      (∑ b, referenceAction (receiverChannel (M := Qubit) D)
        (referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax) X)
        (f, (m, b)) (g, (n, b))) =
        (∑ j, X (f, j) (g, j)) * memory ell m n) := by
  refine ⟨psi_pauli ell, fun j s => ⟨eta_positive hb (hw j) (hmax j) s,
    eta_trace hl hu beta gamma (w j) s⟩,
    fun X f g p q => source_reference ell beta gamma w hl hu hb hw hmax X f g p q,
    fun X f g p q => target_reference ell hl hu X f g p q,
    fun D X f g m n => receiver_memory D X f g m n, ?_⟩
  intro F _ _ B _ _ D X f g m n
  rw [receiver_memory]
  simp_rw [source_reference]
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, omega_memory hl hu]
  exact (Finset.sum_mul _ _ _).symm

end D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
