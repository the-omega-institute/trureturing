/- GID: D5/S3/Quantum/Recovery/PhaseBoundarySourceModel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundarySourceModel
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Flagged recovery source and lossless complete-reference symmetrizations. -/
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
    CStarMatrix.ofMatrix.symm
      ((sourceChannel ell beta gamma w hl hu hb hw hmax).toCompletelyPositiveMap
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

namespace D5.S3.Quantum.Recovery.PhaseBoundaryReferenceReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
private theorem receiver_entry {M A B : Type}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (D : QuantumChannel A B)
    (X : CStarMatrix (M × A) (M × A) ℂ) (p q : M × B) :
    (receiverChannel D).toCompletelyPositiveMap X p q =
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun a b => X (p.1, a) (q.1, b)) p.2 q.2 := by
  exact PhaseBoundarySourceModel.receiver_reference (F := Unit) D
    (CStarMatrix.ofMatrix fun a b => X a.2 b.2) () () p.1 q.1 p.2 q.2
private theorem reference_comp {F A B C : Type}
    [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (G : QuantumChannel A B) (H : QuantumChannel B C)
    (X : CStarMatrix (F × A) (F × A) ℂ) :
    referenceAction (H.comp G) X = referenceAction H (referenceAction G X) := rfl
private theorem receiver_reference {F M A B : Type}
    [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (D : QuantumChannel A B)
    (X : CStarMatrix (F × (M × A)) (F × (M × A)) ℂ)
    (f g : F) (m n : M) (b c : B) :
    referenceAction (receiverChannel D) X (f, (m, b)) (g, (n, c)) =
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun a d => X (f, (m, a)) (g, (n, d))) b c :=
  receiver_entry D _ _ _
private theorem phase_exists {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1) :
    ∃ Z : QuantumChannel A A, ∀ X : CStarMatrix A A ℂ, ∀ a b,
      Z.toCompletelyPositiveMap X a b = (c a : ℂ) * X a b * (c b : ℂ) := by
  let K : Matrix A A ℂ := Matrix.diagonal fun a => (c a : ℂ)
  have hK : (∑ _ : Unit, K.conjTranspose * K) = 1 := by
    simp only [Fintype.sum_unique]
    ext a b
    by_cases hab : a = b
    · subst b
      have hh : (c a : ℂ) ^ 2 = 1 := by exact_mod_cast hc a
      simpa [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        ← pow_two] using hh
    · simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, hab, Ne.symm hab]
  obtain ⟨Z, hZ⟩ := finite_kraus_quantum_channel (fun _ : Unit => K) hK
  refine ⟨Z, fun X a b => ?_⟩
  have hh := congrFun (congrFun (hZ (CStarMatrix.ofMatrix.symm X)) a) b
  simpa [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
    mul_assoc, apply_ite] using hh
private def phaseChannel {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1) : QuantumChannel A A :=
  (phase_exists c hc).choose
private theorem phase_entry {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1)
    (X : CStarMatrix A A ℂ) (a b : A) :
    (phaseChannel c hc).toCompletelyPositiveMap X a b =
      (c a : ℂ) * X a b * (c b : ℂ) :=
  (phase_exists c hc).choose_spec X a b
private theorem sign_square (s : Qubit) : flagSign s ^ 2 = 1 := by
  fin_cases s <;> norm_num [flagSign]
private def inputPhase : QuantumChannel Qubit Qubit := phaseChannel flagSign sign_square
abbrev Output := Qubit × (Qubit × Qubit)
private def outputPhase : QuantumChannel Output Output :=
  phaseChannel (fun p => flagSign p.2.1) (fun p => sign_square p.2.1)
private theorem input_phase_entry (X : CStarMatrix Qubit Qubit ℂ) (a b : Qubit) :
    inputPhase.toCompletelyPositiveMap X a b =
      (flagSign a : ℂ) * X a b * (flagSign b : ℂ) := phase_entry _ _ _ _ _
private theorem output_phase_entry (X : CStarMatrix Output Output ℂ) (a b : Output) :
    outputPhase.toCompletelyPositiveMap X a b =
      (flagSign a.2.1 : ℂ) * X a b * (flagSign b.2.1 : ℂ) := phase_entry _ _ _ _ _

section Source
variable (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
private abbrev N := sourceChannel ell beta gamma w hl hu hb hw hmax
private abbrev V := targetChannel ell hl hu

private theorem source_entry {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) (f g : F) (p q : Output) :
    referenceAction (N ell beta gamma w hl hu hb hw hmax) X (f, p) (g, q) =
      ∑ j, X (f, j) (g, j) * omega ell beta gamma (w j) p q :=
  (phase_boundary_source_complete.{0, 0, 0, 0}
    ell beta gamma w hl hu hb hw hmax).2.2.1 X f g p q
private theorem target_entry {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) (f g : F) (p q : Output) :
    referenceAction (V ell hl hu) X (f, p) (g, q) =
      X (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) * star (xi ell (q.1, q.2.2)) :=
  PhaseBoundarySourceModel.target_reference ell hl hu X f g p q
private abbrev decoded (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :=
  (receiverChannel (M := Qubit) D).comp (N ell beta gamma w hl hu hb hw hmax)

private theorem decoded_pinch {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
    (f g : F) (p q : Output) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax
      (FlagInstrument.extract D).decoder) X (f, p) (g, q) =
      if p.2.1 = q.2.1 then
        referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) X (f, p) (g, q)
      else 0 := by
  let Z := referenceAction (N ell beta gamma w hl hu hb hw hmax) X
  let Y : CStarMatrix ((F × Qubit) × (Qubit × Qubit))
      ((F × Qubit) × (Qubit × Qubit)) ℂ :=
    CStarMatrix.ofMatrix fun a b => Z (a.1.1, (a.1.2, a.2)) (b.1.1, (b.1.2, b.2))
  have hY : FlagDiagonal Y := by
    intro a b hab
    change Z (a.1.1, (a.1.2, a.2)) (b.1.1, (b.1.2, b.2)) = 0
    dsimp only [Z]
    rw [source_entry]
    simp [omega, hab]
  have hh := common_flag_instrument_complete.{0, 0, 0, 0, 0, 0}.2 D (F × Qubit) Y hY
  have he := congrArg (fun T => T ((f, p.1), p.2) ((g, q.1), q.2)) hh
  rcases p with ⟨m, j, a⟩
  rcases q with ⟨n, k, b⟩
  simp only [decoded, reference_comp, receiver_reference]
  exact he
private def twistInput {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) : DensityState (F × Qubit) :=
  (receiverChannel (M := F) inputPhase).mapState rho
private theorem twist_input_entry {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) (f g : F) (a b : Qubit) :
    (twistInput rho).1 (f, a) (g, b) =
      (flagSign a : ℂ) * rho.1 (f, a) (g, b) * (flagSign b : ℂ) := by
  change (receiverChannel inputPhase).toCompletelyPositiveMap rho.1 (f, a) (g, b) = _
  rw [receiver_entry, input_phase_entry]
  rfl

private theorem source_twist {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) :
    referenceAction (N ell beta gamma w hl hu hb hw hmax) (twistInput rho).1 =
      referenceAction (N ell beta gamma w hl hu hb hw hmax) rho.1 := by
  ext ⟨f, p⟩ ⟨g, q⟩
  rw [source_entry, source_entry]
  simp only [twist_input_entry]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (flagSign j : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square j
  linear_combination rho.1 (f, j) (g, j) * omega ell beta gamma (w j) p q * hs

private theorem target_twist {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) :
    (receiverChannel (M := F) outputPhase).toCompletelyPositiveMap
      (referenceAction (V ell hl hu) (twistInput rho).1) =
      referenceAction (V ell hl hu) rho.1 := by
  ext ⟨f, p⟩ ⟨g, q⟩
  rw [receiver_entry, output_phase_entry]
  change (flagSign p.2.1 : ℂ) *
    referenceAction (V ell hl hu) (twistInput rho).1 (f, p) (g, q) *
      (flagSign q.2.1 : ℂ) = _
  simp_rw [target_entry ell hl hu, twist_input_entry]
  have hp : (flagSign p.2.1 : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square p.2.1
  have hq : (flagSign q.2.1 : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square q.2.1
  calc
    _ = ((flagSign p.2.1 : ℂ) ^ 2) * ((flagSign q.2.1 : ℂ) ^ 2) *
      (rho.1 (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) *
        star (xi ell (q.1, q.2.2))) := by ring
    _ = _ := by rw [hp, hq]; ring
private theorem decoded_twist {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) (twistInput rho).1 =
      referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1 := by
  simp only [decoded, reference_comp]
  rw [source_twist]
private theorem symmetrized_state {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax
      (FlagInstrument.extract D).decoder) rho.1 =
      (1 / 2 : ℂ) •
        (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1 +
          (receiverChannel (M := F) outputPhase).toCompletelyPositiveMap
            (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1)) := by
  ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
  rw [decoded_pinch]
  change (if j = k then _ else 0) = (1 / 2 : ℂ) * (_ + _)
  rw [receiver_entry, output_phase_entry]
  fin_cases j <;> fin_cases k <;> simp [flagSign] <;> ring

end Source

private theorem distance_bounded {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) :
    BddAbove ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ rho : DensityState (Fin n × A),
      x = referenceError G H rho}) := by
  refine ⟨2, ?_⟩
  rintro x (hx | ⟨n, rho, rfl⟩)
  · have hx0 : x = 0 := hx
    subst x
    norm_num
  · have hh := traceDistance_le_one (referenceState G rho) (referenceState H rho)
    change referenceError G H rho / 2 ≤ 1 at hh
    linarith
private theorem error_le_distance {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) (n : ℕ) (rho : DensityState (Fin n × A)) :
    referenceError G H rho ≤ diamondDistance G H :=
  le_csSup (distance_bounded G H) (Or.inr ⟨n, rho, rfl⟩)
private theorem distance_nonnegative {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) : 0 ≤ diamondDistance G H :=
  le_csSup (distance_bounded G H) (Or.inl (Set.mem_singleton 0))

/-- Output-label pinching is lossless for the complete-reference minimax error.
The coherent target is kept intact: the comparison uses a phase orbit of the
input, rather than assuming that the target is label diagonal. -/

theorem output_label_symmetrization
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    diamondDistance (decoded ell beta gamma w hl hu hb hw hmax
        (FlagInstrument.extract D).decoder) (targetChannel ell hl hu) ≤
      diamondDistance (decoded ell beta gamma w hl hu hb hw hmax D)
        (targetChannel ell hl hu) := by
  let G := decoded ell beta gamma w hl hu hb hw hmax D
  let S := decoded ell beta gamma w hl hu hb hw hmax (FlagInstrument.extract D).decoder
  let T := targetChannel ell hl hu
  let E := diamondDistance G T
  change sSup _ ≤ E
  apply csSup_le
  · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
  rintro x (hx | ⟨n, rho, rfl⟩)
  · have hh : x = 0 := hx
    subst x
    exact distance_nonnegative G T
  let rho' := twistInput rho
  let Z := receiverChannel (M := Fin n) outputPhase
  let a := referenceState G rho
  let b := referenceState T rho
  let a' := referenceState G rho'
  let b' := referenceState T rho'
  have hA : a'.1 = a.1 := decoded_twist ell beta gamma w hl hu hb hw hmax D rho
  have hB : Z.toCompletelyPositiveMap b'.1 = b.1 :=
    target_twist ell hl hu rho
  let U : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm a.1 - CStarMatrix.ofMatrix.symm b.1
  let W : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm (Z.mapState a').1 - CStarMatrix.ofMatrix.symm (Z.mapState b').1
  have hdiff :
      CStarMatrix.ofMatrix.symm (referenceState S rho).1 - CStarMatrix.ofMatrix.symm b.1 =
        (1 / 2 : ℂ) • (U + W) := by
    have hs := symmetrized_state ell beta gamma w hl hu hb hw hmax D rho
    change referenceAction S rho.1 = (1 / 2 : ℂ) • (a.1 + Z.toCompletelyPositiveMap a.1) at hs
    ext p q
    have he := congrArg (fun X => X p q) hs
    change (referenceState S rho).1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q +
        ((Z.mapState a').1 p q - (Z.mapState b').1 p q))
    change referenceAction S rho.1 p q - b.1 p q = _
    change referenceAction S rho.1 p q =
      (1 / 2 : ℂ) * (a.1 p q + Z.toCompletelyPositiveMap a.1 p q) at he
    change referenceAction S rho.1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q +
        (Z.toCompletelyPositiveMap a'.1 p q - Z.toCompletelyPositiveMap b'.1 p q))
    rw [hA, hB, he]
    ring
  have hU : traceNorm U ≤ E := error_le_distance G T n rho
  have hW : traceNorm W ≤ E := by
    have hc := traceDistance_contract Z a' b'
    change traceNorm W / 2 ≤ referenceError G T rho' / 2 at hc
    have hh := error_le_distance G T n rho'
    linarith
  change traceNorm (CStarMatrix.ofMatrix.symm (referenceState S rho).1 -
    CStarMatrix.ofMatrix.symm b.1) ≤ E
  rw [hdiff]
  obtain ⟨Q, hQ⟩ := (traceNorm_eq_max_re_tr_U ((1 / 2 : ℂ) • (U + W))).1
  have hQU := (traceNorm_eq_max_re_tr_U U).2 ⟨Q, rfl⟩
  have hQW := (traceNorm_eq_max_re_tr_U W).2 ⟨Q, rfl⟩
  have hsplit : (((Q.val * ((1 / 2 : ℂ) • (U + W))).trace).re) =
      (1 / 2 : ℝ) * ((Q.val * U).trace).re +
        (1 / 2 : ℝ) * ((Q.val * W).trace).re := by
    simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [← hQ, hsplit]
  linarith
private def averageChannel {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (G H : QuantumChannel A B) : QuantumChannel A B where
  toCompletelyPositiveMap :=
    { toLinearMap := (1 / 2 : ℂ) •
        (G.toCompletelyPositiveMap.toLinearMap + H.toCompletelyPositiveMap.toLinearMap)
      map_cstarMatrix_nonneg' k X hX := by
        have heq : X.map (⇑((1 / 2 : ℂ) •
            (G.toCompletelyPositiveMap.toLinearMap + H.toCompletelyPositiveMap.toLinearMap))) =
            (1 / 2 : ℂ) • (X.map G.toCompletelyPositiveMap + X.map H.toCompletelyPositiveMap) := by
          ext i j a b
          rfl
        rw [heq]
        exact smul_nonneg (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
          (add_nonneg (G.toCompletelyPositiveMap.map_cstarMatrix_nonneg X hX)
            (H.toCompletelyPositiveMap.map_cstarMatrix_nonneg X hX)) }
  trace_preserving X := by
    change Matrix.trace ((1 / 2 : ℂ) •
      (G.toCompletelyPositiveMap X + H.toCompletelyPositiveMap X)) = Matrix.trace X
    rw [Matrix.trace_smul, Matrix.trace_add, G.trace_preserving, H.trace_preserving]
    ring
private theorem average_entry {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (G H : QuantumChannel A B)
    (X : CStarMatrix A A ℂ) (a b : B) :
    (averageChannel G H).toCompletelyPositiveMap X a b =
      (1 / 2 : ℂ) * (G.toCompletelyPositiveMap X a b + H.toCompletelyPositiveMap X a b) := rfl
private def flipFlag (s : Qubit) : Qubit := if s = 0 then 1 else 0
private theorem flag_conjugation_exists :
    ∃ U : QuantumChannel (Qubit × Qubit) (Qubit × Qubit),
      ∀ (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (p q : Qubit × Qubit),
        U.toCompletelyPositiveMap X p q =
          (flagSign p.2 : ℂ) * X (flipFlag p.1, p.2) (flipFlag q.1, q.2) * (flagSign q.2 : ℂ) := by
  let K : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ := fun p q =>
    if p.1 = flipFlag q.1 ∧ p.2 = q.2 then (flagSign q.2 : ℂ) else 0
  have hK : (∑ _ : Unit, K.conjTranspose * K) = 1 := by
    simp only [Fintype.sum_unique]
    ext ⟨s, a⟩ ⟨t, b⟩
    fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
      norm_num [K, flipFlag, flagSign, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  obtain ⟨U, hU⟩ := finite_kraus_quantum_channel (fun _ : Unit => K) hK
  refine ⟨U, fun X p q => ?_⟩
  have hh := congrFun (congrFun (hU (CStarMatrix.ofMatrix.symm X)) p) q
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;>
    simpa [K, flipFlag, flagSign, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] using hh
private def flagConjugation : QuantumChannel (Qubit × Qubit) (Qubit × Qubit) :=
  flag_conjugation_exists.choose
private theorem flag_conjugation_entry
    (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (p q : Qubit × Qubit) :
    flagConjugation.toCompletelyPositiveMap X p q =
      (flagSign p.2 : ℂ) * X (flipFlag p.1, p.2) (flipFlag q.1, q.2) * (flagSign q.2 : ℂ) :=
  flag_conjugation_exists.choose_spec X p q
private def routPhase : QuantumChannel (Qubit × Qubit) (Qubit × Qubit) :=
  receiverChannel (M := Qubit) inputPhase
private theorem rout_entry (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (p q : Qubit × Qubit) :
    routPhase.toCompletelyPositiveMap X p q = (flagSign p.2 : ℂ) * X p q * (flagSign q.2 : ℂ) := by
  change (receiverChannel inputPhase).toCompletelyPositiveMap X p q = _
  rw [receiver_entry, input_phase_entry]
  rfl
private def jointPhase : QuantumChannel Output Output :=
  phaseChannel (fun p => flagSign p.1 * flagSign p.2.2) (fun p => by
    rw [mul_pow, sign_square, sign_square, one_mul])
private theorem joint_phase_entry (X : CStarMatrix Output Output ℂ) (p q : Output) :
    jointPhase.toCompletelyPositiveMap X p q =
      ((flagSign p.1 * flagSign p.2.2 : ℝ) : ℂ) * X p q *
        ((flagSign q.1 * flagSign q.2.2 : ℝ) : ℂ) := phase_entry _ _ _ _ _

/-- Conjugate only receiver registers by flag-X/R-Z and output-R-Z. -/
def reflectedDecoder (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    QuantumChannel (Qubit × Qubit) (Qubit × Qubit) :=
  routPhase.comp (D.comp flagConjugation)

/-- Average a receiver decoder with its flag-X/R-Z, Rout-Z conjugate.
Both operations act entirely within the receiver's registers. -/
def flagSymmetrizedDecoder (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    QuantumChannel (Qubit × Qubit) (Qubit × Qubit) := averageChannel D (reflectedDecoder D)
private theorem flag_involution
    (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
    flagConjugation.toCompletelyPositiveMap (flagConjugation.toCompletelyPositiveMap X) = X := by
  ext ⟨s, a⟩ ⟨t, b⟩
  simp_rw [flag_conjugation_entry]
  fin_cases s <;> fin_cases a <;> fin_cases t <;> fin_cases b <;> simp [flipFlag, flagSign]
private theorem rout_involution
    (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
    routPhase.toCompletelyPositiveMap (routPhase.toCompletelyPositiveMap X) = X := by
  ext ⟨s, a⟩ ⟨t, b⟩
  simp_rw [rout_entry]
  fin_cases a <;> fin_cases b <;> simp [flagSign]
private theorem reflected_involution (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (X : CStarMatrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
    (reflectedDecoder (reflectedDecoder D)).toCompletelyPositiveMap X =
      D.toCompletelyPositiveMap X := by
  simp only [reflectedDecoder, QuantumChannel.comp_apply]
  rw [flag_involution, rout_involution]

private theorem flag_average_invariant (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    reflectedDecoder (flagSymmetrizedDecoder D) = flagSymmetrizedDecoder D := by
  have hmap : (reflectedDecoder (flagSymmetrizedDecoder D)).toCompletelyPositiveMap =
      (flagSymmetrizedDecoder D).toCompletelyPositiveMap := by
    apply DFunLike.ext
    intro X
    change routPhase.toCompletelyPositiveMap
      ((1 / 2 : ℂ) • (D.toCompletelyPositiveMap (flagConjugation.toCompletelyPositiveMap X) +
        (reflectedDecoder D).toCompletelyPositiveMap (flagConjugation.toCompletelyPositiveMap X))) =
      (1 / 2 : ℂ) • (D.toCompletelyPositiveMap X + (reflectedDecoder D).toCompletelyPositiveMap X)
    rw [map_smul, map_add]
    have hh := reflected_involution D X
    change routPhase.toCompletelyPositiveMap
      ((reflectedDecoder D).toCompletelyPositiveMap (flagConjugation.toCompletelyPositiveMap X)) =
        D.toCompletelyPositiveMap X at hh
    rw [hh]
    change (1 / 2 : ℂ) • ((reflectedDecoder D).toCompletelyPositiveMap X +
      D.toCompletelyPositiveMap X) = _
    rw [add_comm]
  have channel_ext (G H : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
      (h : G.toCompletelyPositiveMap = H.toCompletelyPositiveMap) : G = H := by
    cases G
    cases H
    cases h
    rfl
  exact channel_ext _ _ hmap
private theorem omega_flip (ell beta gamma w : ℝ) (p q : Output) :
    (flagSign p.2.2 : ℂ) *
      omega ell beta gamma w (p.1, (flipFlag p.2.1, p.2.2))
        (q.1, (flipFlag q.2.1, q.2.2)) * (flagSign q.2.2 : ℂ) =
      (flagSign p.1 : ℂ) * omega ell beta gamma w p q * (flagSign q.1 : ℂ) := by
  rcases p with ⟨m, s, a⟩
  rcases q with ⟨n, t, b⟩
  fin_cases m <;> fin_cases s <;> fin_cases a <;>
    fin_cases n <;> fin_cases t <;> fin_cases b <;>
    simp [omega, eta, outer, xi, psi, flipFlag, flagSign, Matrix.vecMulVec_apply] <;> ring

section Flag
variable (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))

private theorem source_block_flip {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) (f g : F) (m n : Qubit) :
    flagConjugation.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun a b => referenceAction (N ell beta gamma w hl hu hb hw hmax)
        X (f, (m, a)) (g, (n, b))) =
      ((flagSign m * flagSign n : ℝ) : ℂ) •
        (CStarMatrix.ofMatrix fun a b => referenceAction (N ell beta gamma w hl hu hb hw hmax)
          X (f, (m, a)) (g, (n, b))) := by
  ext ⟨s, a⟩ ⟨t, b⟩
  rw [flag_conjugation_entry]
  change (flagSign a : ℂ) *
    referenceAction (N ell beta gamma w hl hu hb hw hmax) X
      (f, (m, (flipFlag s, a))) (g, (n, (flipFlag t, b))) * (flagSign b : ℂ) =
    ((flagSign m * flagSign n : ℝ) : ℂ) *
      referenceAction (N ell beta gamma w hl hu hb hw hmax) X (f, (m, (s, a))) (g, (n, (t, b)))
  rw [source_entry, source_entry]
  simp only [Finset.mul_sum, Finset.sum_mul, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination X (f, j) (g, j) * omega_flip ell beta gamma (w j) (m, (s, a)) (n, (t, b))

private theorem decoded_reflection {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax (reflectedDecoder D)) X =
      (receiverChannel (M := F) jointPhase).toCompletelyPositiveMap
        (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) X) := by
  ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
  simp only [decoded, reference_comp, receiver_reference, reflectedDecoder,
    QuantumChannel.comp_apply]
  rw [rout_entry, receiver_entry, joint_phase_entry]
  simp only [CStarMatrix.ofMatrix_apply, receiver_reference]
  change (flagSign a : ℂ) *
    D.toCompletelyPositiveMap (flagConjugation.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix fun c d => referenceAction (N ell beta gamma w hl hu hb hw hmax)
        X (f, (m, c)) (g, (n, d)))) (j, a) (k, b) * (flagSign b : ℂ) =
    ((flagSign m * flagSign a : ℝ) : ℂ) *
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun c d => referenceAction (N ell beta gamma w hl hu hb hw hmax)
          X (f, (m, c)) (g, (n, d))) (j, a) (k, b) *
      ((flagSign n * flagSign b : ℝ) : ℂ)
  rw [source_block_flip, map_smul]
  simp only [CStarMatrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring
private theorem target_joint_invariant {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) :
    (receiverChannel (M := F) jointPhase).toCompletelyPositiveMap
      (referenceAction (V ell hl hu) X) = referenceAction (V ell hl hu) X := by
  ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
  rw [receiver_entry, joint_phase_entry]
  change ((flagSign m * flagSign a : ℝ) : ℂ) *
    referenceAction (V ell hl hu) X (f, (m, (j, a))) (g, (n, (k, b))) *
      ((flagSign n * flagSign b : ℝ) : ℂ) = _
  simp_rw [target_entry]
  fin_cases m <;> fin_cases a <;> fin_cases n <;> fin_cases b <;> simp [xi, flagSign]
private theorem flag_average_state {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax (flagSymmetrizedDecoder D)) X =
      (1 / 2 : ℂ) •
        (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) X +
          (receiverChannel (M := F) jointPhase).toCompletelyPositiveMap
            (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) X)) := by
  rw [← decoded_reflection ell beta gamma w hl hu hb hw hmax D X]
  ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
  simp only [decoded, reference_comp, receiver_reference, flagSymmetrizedDecoder, average_entry]
  change (1 / 2 : ℂ) * (_ + _) = (1 / 2 : ℂ) * (_ + _)
  rw [receiver_reference, receiver_reference]

end Flag

/-- Flag-X/R-Z averaging preserves locality and cannot increase the complete
reference error. The memory phase occurs only in the covariance proof; the
averaged decoder acts on the receiver's flag and qubit alone. -/

theorem flag_z_symmetrization
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    reflectedDecoder (flagSymmetrizedDecoder D) = flagSymmetrizedDecoder D ∧
    diamondDistance (decoded ell beta gamma w hl hu hb hw hmax (flagSymmetrizedDecoder D))
        (targetChannel ell hl hu) ≤
      diamondDistance (decoded ell beta gamma w hl hu hb hw hmax D)
        (targetChannel ell hl hu) := by
  refine ⟨flag_average_invariant D, ?_⟩
  let G := decoded ell beta gamma w hl hu hb hw hmax D
  let S := decoded ell beta gamma w hl hu hb hw hmax (flagSymmetrizedDecoder D)
  let T := targetChannel ell hl hu
  let E := diamondDistance G T
  change sSup _ ≤ E
  apply csSup_le
  · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
  rintro x (hx | ⟨n, rho, rfl⟩)
  · have hh : x = 0 := hx
    subst x
    exact distance_nonnegative G T
  let Z := receiverChannel (M := Fin n) jointPhase
  let a := referenceState G rho
  let b := referenceState T rho
  have hB : Z.toCompletelyPositiveMap b.1 = b.1 := target_joint_invariant ell hl hu rho.1
  let U : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm a.1 - CStarMatrix.ofMatrix.symm b.1
  let W : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm (Z.mapState a).1 - CStarMatrix.ofMatrix.symm (Z.mapState b).1
  have hdiff :
      CStarMatrix.ofMatrix.symm (referenceState S rho).1 - CStarMatrix.ofMatrix.symm b.1 =
        (1 / 2 : ℂ) • (U + W) := by
    have hs := flag_average_state ell beta gamma w hl hu hb hw hmax D rho.1
    change referenceAction S rho.1 = (1 / 2 : ℂ) • (a.1 + Z.toCompletelyPositiveMap a.1) at hs
    ext p q
    have he := congrArg (fun X => X p q) hs
    change (referenceState S rho).1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q + ((Z.mapState a).1 p q - (Z.mapState b).1 p q))
    change referenceAction S rho.1 p q - b.1 p q = _
    change referenceAction S rho.1 p q =
      (1 / 2 : ℂ) * (a.1 p q + Z.toCompletelyPositiveMap a.1 p q) at he
    change referenceAction S rho.1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q +
        (Z.toCompletelyPositiveMap a.1 p q - Z.toCompletelyPositiveMap b.1 p q))
    rw [hB, he]
    ring
  have hU : traceNorm U ≤ E := error_le_distance G T n rho
  have hW : traceNorm W ≤ E := by
    have hc := traceDistance_contract Z a b
    change traceNorm W / 2 ≤ referenceError G T rho / 2 at hc
    have hh := error_le_distance G T n rho
    linarith
  change traceNorm (CStarMatrix.ofMatrix.symm (referenceState S rho).1 -
    CStarMatrix.ofMatrix.symm b.1) ≤ E
  rw [hdiff]
  obtain ⟨Q, hQ⟩ := (traceNorm_eq_max_re_tr_U ((1 / 2 : ℂ) • (U + W))).1
  have hQU := (traceNorm_eq_max_re_tr_U U).2 ⟨Q, rfl⟩
  have hQW := (traceNorm_eq_max_re_tr_U W).2 ⟨Q, rfl⟩
  have hsplit : (((Q.val * ((1 / 2 : ℂ) • (U + W))).trace).re) =
      (1 / 2 : ℝ) * ((Q.val * U).trace).re + (1 / 2 : ℝ) * ((Q.val * W).trace).re := by
    simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [← hQ, hsplit]
  linarith
end D5.S3.Quantum.Recovery.PhaseBoundaryReferenceReduction
