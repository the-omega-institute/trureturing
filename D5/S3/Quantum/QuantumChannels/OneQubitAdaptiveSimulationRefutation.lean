/- GID: D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.claim; result=D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result; claim=D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.claim
   digest: A sign-frame channel obstructs bounded-round simulation with one ancilla qubit. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Matrix.RecordCapacity

/-!
Finite adaptive protocols on a system and a qubit, with a diagonal-Kraus obstruction
to uniform positive success at bounded measurement depth.
-/

noncomputable section

open Matrix Complex
open scoped BigOperators ComplexConjugate CStarAlgebra ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.OneQubitAdaptiveSimulationRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel

abbrev Workspace (ι : Type) := CStarMatrix (ι × Fin 2) (ι × Fin 2) ℂ

/-- A joint projective measurement with finitely many, possibly zero, outcomes. -/
structure Measurement (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℕ) where
  projector : Fin k → Workspace ι
  projection : ∀ o, IsStarProjection (projector o)
  orthogonal : ∀ o o', o ≠ o' → projector o * projector o' = 0
  complete : ∑ o, projector o = 1

/-- An adaptive tree whose branches contain at most the indicated number of measurements. -/
inductive Protocol (ι : Type) [Fintype ι] [DecidableEq ι] : ℕ → Type
  | leaf {R : ℕ} (success : Bool) : Protocol ι R
  | node {R : ℕ} (k : ℕ) (U : unitary (Workspace ι))
      (P : Measurement ι k) (child : Fin k → Protocol ι R) : Protocol ι (R + 1)

namespace Protocol

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def History : {R : ℕ} → Protocol ι R → Type
  | _, .leaf _ => Unit
  | _, .node k _ _ child => (o : Fin k) × History (child o)

instance historyFintype : {R : ℕ} → (t : Protocol ι R) → Fintype t.History
  | _, .leaf _ => inferInstanceAs (Fintype Unit)
  | _, .node _ _ _ child => by
      letI := fun o => historyFintype (child o)
      exact inferInstanceAs (Fintype (Sigma fun o => (child o).History))

def succeeds : {R : ℕ} → (t : Protocol ι R) → t.History → Bool
  | _, .leaf b, _ => b
  | _, .node _ _ _ child, h => succeeds (child h.1) h.2

/-- The ordered operator product along a measurement history. -/
def branch : {R : ℕ} → (t : Protocol ι R) → t.History → Workspace ι
  | _, .leaf _, _ => 1
  | _, .node _ U P child, h => branch (child h.1) h.2 * P.projector h.1 * U

/-- Compression against the initial ancilla state and a final ancilla basis vector. -/
def krausFrom {R : ℕ} (t : Protocol ι R) (B : Workspace ι)
    (h : t.History) (a : Fin 2) : Matrix ι ι ℂ :=
  if t.succeeds h then
    (CStarMatrix.ofMatrix.symm (t.branch h * B)).submatrix (fun i => (i, a))
      (fun j => (j, 0))
  else 0

def successfulMap {R : ℕ} (t : Protocol ι R) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ h, ∑ a, t.krausFrom 1 h a * X * (t.krausFrom 1 h a)ᴴ

end Protocol

/-- A finite probability distribution over bounded-depth adaptive trees. -/
structure RandomizedProtocol (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ) where
  seeds : ℕ
  probability : Fin seeds → ℝ
  nonnegative : ∀ s, 0 ≤ probability s
  total : ∑ s, probability s = 1
  tree : Fin seeds → Protocol ι R

def RandomizedProtocol.successfulMap {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : ℕ} (p : RandomizedProtocol ι R) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ s, (p.probability s : ℂ) • (p.tree s).successfulMap X

/-- Universal finite depth and a dimension-independent positive success probability. -/
def claim : Prop :=
  ∃ R₀ : ℕ, ∃ q₀ : ℝ, 0 < q₀ ∧
    ∀ d : ℕ, ∀ Φ : QuantumChannel (Fin d) (Fin d),
      ∃ p : RandomizedProtocol (Fin d) R₀, ∃ q : ℝ,
        q₀ ≤ q ∧
        ∀ X : Matrix (Fin d) (Fin d) ℂ,
          p.successfulMap X = (q : ℂ) •
            CStarMatrix.ofMatrix.symm
              (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

abbrev FrameIndex (n : ℕ) := Fin (n * n) ⊕ (Fin (n * n) → Bool)

def sign (b : Bool) : ℂ := if b then 1 else -1

/-- The basis rows and all sign rows of the correlation frame. -/
def frame (n : ℕ) : Matrix (FrameIndex n) (Fin (n * n)) ℂ
  | .inl i, j => if i = j then 1 else 0
  | .inr s, j => sign (s j) / n

def frameNat (n : ℕ) :
    Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (n * n)) ℂ :=
  (frame n).submatrix (Fintype.equivFin (FrameIndex n)).symm id

private theorem measurement_rank_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (P : Measurement ι k) :
    (∑ o, (CStarMatrix.ofMatrix.symm (P.projector o)).rank) = 2 * Fintype.card ι := by
  let f := Matrix.toLinAlgEquiv' (R := ℂ) (n := ι × Fin 2)
  have hid (o : Fin k) :
      IsIdempotentElem (f (CStarMatrix.ofMatrix.symm (P.projector o))) :=
    (P.projection o).isIdempotentElem.map f
  have hsum : (∑ o, f (CStarMatrix.ofMatrix.symm (P.projector o))) = 1 := by
    rw [← map_sum]
    change f (CStarMatrix.ofMatrix.symm (∑ o, P.projector o)) = 1
    rw [P.complete]
    exact f.map_one
  have h :=
    D5.S3.Quantum.Matrix.RecordCapacity.sum_range_finrank_of_idempotent_sum
      (fun o => f (CStarMatrix.ofMatrix.symm (P.projector o))) hid hsum
  change (∑ o, (CStarMatrix.ofMatrix.symm (P.projector o)).rank) =
    Module.finrank ℂ ((ι × Fin 2) → ℂ) at h
  simpa [Module.finrank_pi, Fintype.card_prod, mul_comm] using h

private theorem measurement_few_large {ι : Type} [Fintype ι] [DecidableEq ι]
    {k r : ℕ} (P : Measurement ι k) (hr : 2 * Fintype.card ι < 5 * r)
    (S : Finset (Fin k))
    (hS : ∀ o ∈ S, r ≤ (CStarMatrix.ofMatrix.symm (P.projector o)).rank) :
    S.card ≤ 4 := by
  have h₁ : S.card * r ≤ ∑ o ∈ S, (CStarMatrix.ofMatrix.symm (P.projector o)).rank := by
    simpa using Finset.sum_le_sum hS
  have h₂ : (∑ o ∈ S, (CStarMatrix.ofMatrix.symm (P.projector o)).rank) ≤
      ∑ o, (CStarMatrix.ofMatrix.symm (P.projector o)).rank :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  rw [measurement_rank_sum] at h₂
  by_contra h
  have : 5 ≤ S.card := by omega
  nlinarith

private theorem branch_norm {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {R : ℕ} (t : Protocol ι R) (h : t.History) : ‖t.branch h‖ ≤ 1 := by
  induction t with
  | leaf b => exact norm_one.le
  | node k U P child ih =>
      change ‖((child h.1).branch h.2 * P.projector h.1) * (U : Workspace ι)‖ ≤ 1
      rw [CStarRing.norm_mul_coe_unitary]
      exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (ih h.1 h.2)).trans
          ((P.projection h.1).norm_le _))

private theorem kraus_entry_le_one {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {R : ℕ} (t : Protocol ι R) (h : t.History) (a : Fin 2) (i j : ι) :
    ‖t.krausFrom 1 h a i j‖ ≤ 1 := by
  unfold Protocol.krausFrom
  split
  · change ‖(t.branch h * 1) (i, a) (j, 0)‖ ≤ 1
    rw [mul_one]
    exact CStarMatrix.norm_entry_le_norm.trans (branch_norm t h)
  · simp only [Matrix.zero_apply, norm_zero, zero_le_one]

private theorem krausFrom_node {ι : Type} [Fintype ι] [DecidableEq ι]
    {R k : ℕ} (U : unitary (Workspace ι)) (P : Measurement ι k)
    (child : Fin k → Protocol ι R) (B : Workspace ι)
    (o : Fin k) (h : (child o).History) (a : Fin 2) :
    (Protocol.node k U P child).krausFrom B ⟨o, h⟩ a =
      (child o).krausFrom (P.projector o * U * B) h a := by
  unfold Protocol.krausFrom
  change (if (child o).succeeds h then _ else _) =
    (if (child o).succeeds h then _ else _)
  split
  · change (CStarMatrix.ofMatrix.symm
        ((child o).branch h * P.projector o * (U : Workspace ι) * B)).submatrix _ _ = _
    rw [mul_assoc, mul_assoc, mul_assoc]
  · rfl

private theorem krausFrom_rank {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : ℕ} (t : Protocol ι R) (B : Workspace ι) (h : t.History) (a : Fin 2) :
    (t.krausFrom B h a).rank ≤ (CStarMatrix.ofMatrix.symm B).rank := by
  unfold Protocol.krausFrom
  split
  · exact (Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_mul_le_right _ _)
  · simp only [Matrix.rank_zero, Nat.zero_le]

private def usefulCount {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : ℕ} (t : Protocol ι R) (B : Workspace ι) : ℕ :=
  ∑ h, if ∃ a, t.krausFrom B h a ≠ 0 then 1 else 0

private theorem usefulCount_node {ι : Type} [Fintype ι] [DecidableEq ι]
    {R k : ℕ} (U : unitary (Workspace ι)) (P : Measurement ι k)
    (child : Fin k → Protocol ι R) (B : Workspace ι) :
    usefulCount (.node k U P child) B =
      ∑ o, usefulCount (child o) (P.projector o * U * B) := by
  unfold usefulCount
  change (∑ h : (o : Fin k) × (child o).History, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro h _
  simp only [krausFrom_node]

private theorem usefulCount_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {R r : ℕ} (t : Protocol ι R) (B : Workspace ι)
    (hr : 2 * Fintype.card ι < 5 * r)
    (hK : ∀ h a, t.krausFrom B h a ≠ 0 → r ≤ (t.krausFrom B h a).rank) :
    usefulCount t B ≤ 4 ^ R := by
  induction t generalizing B with
  | @leaf R b =>
      unfold usefulCount
      change (∑ h : Unit, _) ≤ _
      rw [Fintype.sum_unique]
      split <;> simp_all [Nat.one_le_pow]
  | @node R k U P child ih =>
      rw [usefulCount_node]
      let S := Finset.univ.filter fun o =>
        0 < usefulCount (child o) (P.projector o * U * B)
      have hS : S.card ≤ 4 := by
        apply measurement_few_large P hr S
        intro o ho
        have hc := (Finset.mem_filter.mp ho).2
        change 0 < ∑ h, if ∃ a, (child o).krausFrom
          (P.projector o * U * B) h a ≠ 0 then 1 else 0 at hc
        obtain ⟨h, _, hhpos⟩ := Finset.sum_pos_iff.mp hc
        by_cases hh : ∃ a, (child o).krausFrom (P.projector o * U * B) h a ≠ 0
        · obtain ⟨a, ha⟩ := hh
          have hk := hK ⟨o, h⟩ a (by rw [krausFrom_node]; exact ha)
          rw [krausFrom_node] at hk
          exact hk.trans ((krausFrom_rank _ _ _ _).trans
            ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)))
        · simp only [ite_eq_right hh, lt_self_iff_false] at hhpos
      calc
        _ = ∑ o ∈ S, usefulCount (child o) (P.projector o * U * B) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro o _ ho
          exact Nat.eq_zero_of_not_pos (fun hc =>
            ho (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
        _ ≤ ∑ _o ∈ S, 4 ^ R := by
          apply Finset.sum_le_sum
          intro o _
          apply ih o _
          intro h a ha
          have hk := hK ⟨o, h⟩ a (by rw [krausFrom_node]; exact ha)
          rw [krausFrom_node] at hk
          exact hk
        _ ≤ 4 * 4 ^ R := by simpa using Nat.mul_le_mul_right (4 ^ R) hS
        _ = _ := by rw [pow_succ, Nat.mul_comm]

private theorem frame_basis (n : ℕ) (v : Fin (n * n) → ℂ) (j : Fin (n * n)) :
    (frame n *ᵥ v) (.inl j) = v j := by
  simp [frame, Matrix.mulVec, dotProduct]

private theorem frame_sign (n : ℕ) (v : Fin (n * n) → ℂ) (s : Fin (n * n) → Bool) :
    (frame n *ᵥ v) (.inr s) = (∑ j, sign (s j) * v j) / n := by
  simp only [Matrix.mulVec, dotProduct, frame, div_mul_eq_mul_div, Finset.sum_div]

private theorem frame_row_complete (n : ℕ) (hn : 0 < n) (i : FrameIndex n) :
    (∑ j, star (frame n i j) * frame n i j) = 1 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  cases i with
  | inl i => simp [frame]
  | inr s =>
      have hs (b : Bool) : star (sign b) * sign b = 1 := by
        cases b <;> norm_num [sign]
      simp only [frame, star_div₀, star_natCast, div_mul_div_comm, hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp

private theorem frame_complete (n : ℕ) (hn : 0 < n) :
    (∑ j, (Matrix.diagonal (frameNat n · j))ᴴ * Matrix.diagonal (frameNat n · j)) = 1 := by
  ext i l
  by_cases hil : i = l
  · subst l
    simp only [Matrix.sum_apply, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact frame_row_complete n hn ((Fintype.equivFin (FrameIndex n)).symm i)
  · simp [Matrix.sum_apply, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, hil]

private def frameChannel (n : ℕ) (hn : 0 < n) :
    QuantumChannel (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) :=
  Classical.choose (finite_kraus_quantum_channel
    (fun j => Matrix.diagonal (frameNat n · j)) (frame_complete n hn))

private theorem frameChannel_action (n : ℕ) (hn : 0 < n)
    (X : Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ) :
    CStarMatrix.ofMatrix.symm
      ((frameChannel n hn).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ j, Matrix.diagonal (frameNat n · j) * X * (Matrix.diagonal (frameNat n · j))ᴴ :=
  Classical.choose_spec (finite_kraus_quantum_channel
    (fun j => Matrix.diagonal (frameNat n · j)) (frame_complete n hn)) X

private theorem coefficient_budget (n : ℕ) (hn : 0 < n) (v : Fin (n * n) → ℂ)
    (hv : ∀ i, ‖(frame n *ᵥ v) i‖ ≤ 1) :
    (∑ j, Complex.normSq (v j)) ≤ 2 * n := by
  have hcoord (j) : ‖v j‖ ≤ 1 := by simpa only [frame_basis] using hv (.inl j)
  have hsign (s : Fin (n * n) → Bool) : ‖∑ j, sign (s j) * v j‖ ≤ n := by
    have h := hv (.inr s)
    rw [frame_sign, norm_div, Complex.norm_natCast] at h
    exact (div_le_one (by exact_mod_cast hn)).mp h
  have hre : (∑ j, |(v j).re|) ≤ n := by
    have h := (Complex.re_le_norm _).trans (hsign (fun j => decide (0 ≤ (v j).re)))
    convert h using 1
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 0 ≤ (v j).re
    · simp [sign, h, abs_of_nonneg h]
    · simp [sign, h, abs_of_neg (lt_of_not_ge h)]
  have him : (∑ j, |(v j).im|) ≤ n := by
    have h := (Complex.im_le_norm _).trans (hsign (fun j => decide (0 ≤ (v j).im)))
    convert h using 1
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 0 ≤ (v j).im
    · simp [sign, h, abs_of_nonneg h]
    · simp [sign, h, abs_of_neg (lt_of_not_ge h)]
  calc
    _ ≤ ∑ j, ‖v j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [hcoord j, norm_nonneg (v j)]
    _ ≤ ∑ j, (|(v j).re| + |(v j).im|) :=
      Finset.sum_le_sum fun j _ => Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * n := by rw [Finset.sum_add_distrib]; linarith

private theorem frame_rank (n : ℕ) (hn : 0 < n) (v : Fin (n * n) → ℂ) (hv : v ≠ 0) :
    2 ^ (n * n - 1) + 1 ≤ (Matrix.diagonal (frame n *ᵥ v)).rank := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  let e := Equiv.funSplitAt j Bool
  have hat (b : Bool) (s : {k : Fin (n * n) // k ≠ j} → Bool) :
      e.symm (b, s) j = b := congrArg Prod.fst (e.apply_symm_apply (b, s))
  have hoff (b : Bool) (s : {k : Fin (n * n) // k ≠ j} → Bool)
      (k : {k : Fin (n * n) // k ≠ j}) : e.symm (b, s) k = s k :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply (b, s))) k
  have hpair (s : {k : Fin (n * n) // k ≠ j} → Bool) :
      ∃ b : Bool, (frame n *ᵥ v) (.inr (e.symm (b, s))) ≠ 0 := by
    have hd : (frame n *ᵥ v) (.inr (e.symm (true, s))) -
        (frame n *ᵥ v) (.inr (e.symm (false, s))) = 2 * v j / n := by
      rw [frame_sign, frame_sign, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      calc
        _ = ∑ k, if k = j then 2 * v j else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : k = j
          · subst k
            rw [hat, hat]
            norm_num [sign]
            ring
          · have h₁ := hoff true s ⟨k, hk⟩
            have h₂ := hoff false s ⟨k, hk⟩
            rw [h₁, h₂, sub_self, ite_eq_right hk]
        _ = _ := by simp
    by_contra h
    push Not at h
    rw [h true, h false, sub_self] at hd
    exact (div_ne_zero (mul_ne_zero (by norm_num) hj)
      (by exact_mod_cast hn.ne')) hd.symm
  choose b hb using hpair
  let f : Unit ⊕ ({k : Fin (n * n) // k ≠ j} → Bool) →
      {i : FrameIndex n // (frame n *ᵥ v) i ≠ 0}
    | .inl _ => ⟨.inl j, by rw [frame_basis]; exact hj⟩
    | .inr s => ⟨.inr (e.symm (b s, s)), hb s⟩
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg Subtype.val h
    cases x with
    | inl x =>
        cases y with
        | inl y => rfl
        | inr t => cases h'
    | inr s =>
        cases y with
        | inl y => cases h'
        | inr t =>
            have he := congrArg e (Sum.inr.inj h')
            rw [e.apply_symm_apply, e.apply_symm_apply] at he
            exact congrArg Sum.inr (congrArg Prod.snd he)
  have hc : Fintype.card {k : Fin (n * n) // k ≠ j} = n * n - 1 := by simp
  have hh := Fintype.card_le_of_injective f hf
  rw [Matrix.rank_diagonal]
  simpa [Fintype.card_sum, Fintype.card_fun, hc, Nat.add_comm] using hh

private theorem frame_rank_gap (n : ℕ) (hn : 2 ≤ n) :
    2 * Fintype.card (FrameIndex n) < 5 * (2 ^ (n * n - 1) + 1) := by
  have he : ∀ m : ℕ, 4 ≤ m → 2 * m ≤ 2 ^ (m - 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
        have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ m)]
          rw [pow_succ, Nat.mul_comm]
        simpa only [Nat.add_sub_cancel] using
          (show 2 * (m + 1) ≤ 2 ^ m by nlinarith)
  have hm : 4 ≤ n * n := by nlinarith
  have hh := he (n * n) hm
  have hp : 2 ^ (n * n) = 2 * 2 ^ (n * n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n * n)]
    rw [pow_succ, Nat.mul_comm]
  simp only [FrameIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool]
  nlinarith

private theorem sandwich_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (i j : ι) :
    (K * (Matrix.single j j (1 : ℂ) : Matrix ι ι ℂ) * Kᴴ) i i =
      (Complex.normSq (K i j) : ℂ) := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Matrix.conjTranspose_apply,
    Complex.mul_conj]

private theorem zero_weighted_normSq {κ : Type} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (w : κ → ℂ)
    (hz : ∑ k, p k * Complex.normSq (w k) = 0) (k : κ) (hk : 0 < p k) : w k = 0 := by
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_nonneg (hp k) (Complex.normSq_nonneg _))).mp hz k (Finset.mem_univ k)
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hk.ne')

private theorem exact_diagonal {ι κ μ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype μ] (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (K : κ → Matrix ι ι ℂ) (A : Matrix ι μ ℂ) (q : ℝ)
    (heq : ∀ X, (∑ k, (p k : ℂ) • (K k * X * (K k)ᴴ)) =
      (q : ℂ) • ∑ j, Matrix.diagonal (A · j) * X * (Matrix.diagonal (A · j))ᴴ)
    (k : κ) (hk : 0 < p k) : K k = Matrix.diagonal (Matrix.diag (K k)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp only [Matrix.diagonal_apply_eq, Matrix.diag_apply]
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply zero_weighted_normSq p hp (fun k => K k i j) _ k hk
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re)
      (heq (Matrix.single j j 1))
    simpa only [Matrix.sum_apply, Matrix.smul_apply, sandwich_single,
      Matrix.diagonal_apply_ne _ hij, Complex.normSq_zero, Complex.ofReal_zero,
      mul_zero, Finset.sum_const_zero, smul_zero, Complex.zero_re, Complex.re_sum,
      smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re] using h

private theorem exact_gram {ι κ μ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype μ] (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (K : κ → Matrix ι ι ℂ) (A : Matrix ι μ ℂ) (q : ℝ)
    (heq : ∀ X, (∑ k, (p k : ℂ) • (K k * X * (K k)ᴴ)) =
      (q : ℂ) • ∑ j, Matrix.diagonal (A · j) * X * (Matrix.diagonal (A · j))ᴴ) :
    (∑ k, (p k : ℂ) • Matrix.vecMulVec (Matrix.diag (K k)) (star (Matrix.diag (K k)))) =
      (q : ℂ) • (A * Aᴴ) := by
  have hdiag (k) (hk : 0 < p k) := exact_diagonal p hp K A q heq k hk
  let J : Matrix ι ι ℂ := Matrix.of fun _ _ => 1
  have hsand (w : ι → ℂ) :
      Matrix.diagonal w * J * (Matrix.diagonal w)ᴴ =
        Matrix.vecMulVec w (star w) := by
    ext i j
    simp [J, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_conjTranspose, Matrix.vecMulVec]
  calc
    _ = ∑ k, (p k : ℂ) • (K k * J * (K k)ᴴ) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : p k = 0
      · rw [hk]; simp
      · rw [hdiag k (lt_of_le_of_ne (hp k) (Ne.symm hk)), hsand]
        simp only [Matrix.diag_diagonal]
    _ = _ := by
      rw [heq]
      congr 1
      simp only [hsand]
      ext i j
      simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec,
        Pi.star_apply]

private theorem gram_kernel {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (w : κ → ι → ℂ)
    (A : Matrix ι μ ℂ) (q : ℝ)
    (heq : (∑ k, (p k : ℂ) • Matrix.vecMulVec (w k) (star (w k))) =
      (q : ℂ) • (A * Aᴴ))
    (z : ι → ℂ) (hz : z ᵥ* A = 0) (k : κ) (hk : 0 < p k) : z ⬝ᵥ w k = 0 := by
  have hout (v : ι → ℂ) : z ⬝ᵥ (Matrix.vecMulVec v (star v) *ᵥ star z) =
      (Complex.normSq (z ⬝ᵥ v) : ℂ) := by
    rw [dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct,
      star_dotProduct_star, smul_eq_mul, Complex.star_def, Complex.mul_conj]
  have hzero : z ⬝ᵥ ((A * Aᴴ) *ᵥ star z) = 0 := by
    rw [dotProduct_mulVec, ← Matrix.vecMul_vecMul, hz, Matrix.zero_vecMul, zero_dotProduct]
  have h := congrArg (fun M : Matrix ι ι ℂ => z ⬝ᵥ (M *ᵥ star z)) heq
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    hout, hzero, smul_eq_mul, ← Complex.ofReal_mul] at h
  apply zero_weighted_normSq p hp (fun k => z ⬝ᵥ w k) _ k hk
  simpa only [Complex.re_sum, Complex.ofReal_re, mul_zero, Complex.zero_re]
    using congrArg Complex.re h

private def coefficients (n : ℕ)
    (K : Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ)
    (j : Fin (n * n)) : ℂ :=
  K ((Fintype.equivFin (FrameIndex n)) (.inl j)) ((Fintype.equivFin (FrameIndex n)) (.inl j))

private theorem frameNat_basis (n : ℕ) (i j : Fin (n * n)) :
    frameNat n ((Fintype.equivFin (FrameIndex n)) (.inl i)) j = if i = j then 1 else 0 := by
  simp only [frameNat, Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq, frame]

private theorem frameNat_sign (n : ℕ) (s : Fin (n * n) → Bool) (j : Fin (n * n)) :
    frameNat n ((Fintype.equivFin (FrameIndex n)) (.inr s)) j = sign (s j) / n := by
  simp only [frameNat, Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq, frame]

private theorem exact_frame_span (n : ℕ) {κ : Type} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (K : κ → Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ)
    (q : ℝ)
    (heq : ∀ X, (∑ k, (p k : ℂ) • (K k * X * (K k)ᴴ)) =
      (q : ℂ) • ∑ j, Matrix.diagonal (frameNat n · j) * X *
        (Matrix.diagonal (frameNat n · j))ᴴ)
    (k : κ) (hk : 0 < p k) :
    K k = Matrix.diagonal (frameNat n *ᵥ coefficients n (K k)) := by
  classical
  let e := Fintype.equivFin (FrameIndex n)
  have hg := exact_gram p hp K (frameNat n) q heq
  apply (exact_diagonal p hp K (frameNat n) q heq k hk).trans
  congr 1
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  cases i with
  | inl j =>
      simp [e, Matrix.diag_apply, Matrix.mulVec, dotProduct, frameNat_basis, coefficients]
  | inr s =>
      let z := Pi.single (e (.inr s)) (1 : ℂ) -
        ∑ j, (sign (s j) / n) • Pi.single (e (.inl j)) (1 : ℂ)
      have hz : z ᵥ* frameNat n = 0 := by
        simp only [z, Matrix.sub_vecMul, Matrix.sum_vecMul, Matrix.smul_vecMul,
          Matrix.single_vecMul, one_smul]
        ext j
        simp [Matrix.row, Pi.sub_apply, frameNat_basis, frameNat_sign, e]
      have h := gram_kernel p hp (fun k => Matrix.diag (K k)) (frameNat n) q hg z hz k hk
      simp only [z, sub_dotProduct, sum_dotProduct, smul_dotProduct,
        single_dotProduct, one_mul] at h
      have hh := sub_eq_zero.mp h
      change (K k).diag (e (.inr s)) = _
      apply hh.trans
      simp only [Matrix.mulVec, dotProduct, e, frameNat_sign, coefficients,
        Matrix.diag_apply, smul_eq_mul]

private theorem frameNat_rank (n : ℕ) (hn : 0 < n) (v : Fin (n * n) → ℂ) (hv : v ≠ 0) :
    2 ^ (n * n - 1) + 1 ≤ (Matrix.diagonal (frameNat n *ᵥ v)).rank := by
  let e := Fintype.equivFin (FrameIndex n)
  have h : (Matrix.diagonal (frameNat n *ᵥ v)).submatrix e e =
      Matrix.diagonal (frame n *ᵥ v) := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, frameNat,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq, e]
  exact (frame_rank n hn v hv).trans_eq
    (by rw [← h, Matrix.rank_submatrix])

private def coefficientEnergy (n : ℕ)
    (K : Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ) : ℝ :=
  ∑ j, Complex.normSq (coefficients n K j)

private theorem frameNat_budget (n : ℕ) (hn : 0 < n)
    (K : Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ)
    (hK : K = Matrix.diagonal (frameNat n *ᵥ coefficients n K))
    (hentry : ∀ i, ‖K i i‖ ≤ 1) : coefficientEnergy n K ≤ 2 * n := by
  apply coefficient_budget n hn
  intro i
  have h := hentry ((Fintype.equivFin (FrameIndex n)) i)
  rw [hK, Matrix.diagonal_apply_eq] at h
  simpa only [Matrix.mulVec, dotProduct, frameNat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id_eq] using h

private theorem tree_energy_bound (n : ℕ) (hn : 2 ≤ n) {R : ℕ}
    (t : Protocol (Fin (Fintype.card (FrameIndex n))) R)
    (hspan : ∀ h a, t.krausFrom 1 h a =
      Matrix.diagonal (frameNat n *ᵥ coefficients n (t.krausFrom 1 h a))) :
    (∑ h, ∑ a, coefficientEnergy n (t.krausFrom 1 h a)) ≤ 4 * n * (4 : ℝ) ^ R := by
  classical
  have : Nonempty (Fin (Fintype.card (FrameIndex n))) := ⟨⟨0, Fintype.card_pos⟩⟩
  have hbudget (h) (a) : coefficientEnergy n (t.krausFrom 1 h a) ≤ 2 * n :=
    frameNat_budget n (by omega) _ (hspan h a) (fun i => kraus_entry_le_one t h a i i)
  have hc := usefulCount_bound t 1
    (by simpa only [Fintype.card_fin] using frame_rank_gap n hn) (fun h a hne => by
    have hv : coefficients n (t.krausFrom 1 h a) ≠ 0 := by
      intro hz
      apply hne
      rw [hspan h a, hz, Matrix.mulVec_zero]
      exact Matrix.diagonal_zero
    rw [hspan h a]
    exact frameNat_rank n (by omega) _ hv)
  have hzero : coefficientEnergy n (0 : Matrix (Fin (Fintype.card (FrameIndex n)))
      (Fin (Fintype.card (FrameIndex n))) ℂ) = 0 := by
    simp [coefficientEnergy, coefficients]
  have hsum : (∑ h, ∑ a, coefficientEnergy n (t.krausFrom 1 h a)) ≤
      (4 * n : ℝ) * usefulCount t 1 := by
    calc
      _ ≤ ∑ h, if ∃ a, t.krausFrom 1 h a ≠ 0 then (4 * n : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro h _
        split_ifs with hh
        · rw [Fin.sum_univ_two]
          linarith [hbudget h 0, hbudget h 1]
        · have hz (a : Fin 2) : t.krausFrom 1 h a = 0 :=
            not_not.mp (not_exists.mp hh a)
          simp only [hz, hzero, Finset.sum_const_zero, le_refl]
      _ = _ := by
        unfold usefulCount
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
  exact hsum.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity))

private theorem frame_energy_identity (n : ℕ) {κ : Type} [Fintype κ]
    (p : κ → ℝ)
    (K : κ → Matrix (Fin (Fintype.card (FrameIndex n))) (Fin (Fintype.card (FrameIndex n))) ℂ)
    (q : ℝ)
    (heq : ∀ X, (∑ k, (p k : ℂ) • (K k * X * (K k)ᴴ)) =
      (q : ℂ) • ∑ j, Matrix.diagonal (frameNat n · j) * X *
        (Matrix.diagonal (frameNat n · j))ᴴ) :
    (∑ k, p k * coefficientEnergy n (K k)) = q * (n : ℝ) ^ 2 := by
  have hb (j : Fin (n * n)) :
      (∑ k, p k * Complex.normSq (coefficients n (K k) j)) = q := by
    let i := (Fintype.equivFin (FrameIndex n)) (.inl j)
    have h := congrArg (fun M => (M i i).re) (heq (Matrix.single i i 1))
    simpa only [Matrix.sum_apply, Matrix.smul_apply, sandwich_single,
      Matrix.diagonal_apply_eq, frameNat_basis, i, coefficients, Complex.re_sum,
      smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re, apply_ite,
      Complex.normSq_one, Complex.normSq_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Complex.ofReal_zero, Complex.ofReal_one, mul_one] using h
  calc
    _ = ∑ j, ∑ k, p k * Complex.normSq (coefficients n (K k) j) := by
      simp only [coefficientEnergy, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ _j : Fin (n * n), q := by simp only [hb]
    _ = _ := by simp [pow_two]; ring

private theorem simulation_bound (n : ℕ) (hn : 2 ≤ n) {R : ℕ}
    (p : RandomizedProtocol (Fin (Fintype.card (FrameIndex n))) R) (q : ℝ)
    (heq : ∀ X, p.successfulMap X = (q : ℂ) •
      CStarMatrix.ofMatrix.symm
        ((frameChannel n (by omega)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) :
    q * n ≤ 4 * (4 : ℝ) ^ R := by
  classical
  let κ := (s : Fin p.seeds) × (p.tree s).History × Fin 2
  let K : κ → Matrix (Fin (Fintype.card (FrameIndex n)))
      (Fin (Fintype.card (FrameIndex n))) ℂ := fun k =>
    (p.tree k.1).krausFrom 1 k.2.1 k.2.2
  let w : κ → ℝ := fun k => p.probability k.1
  have hw (k) : 0 ≤ w k := p.nonnegative k.1
  have hmap : ∀ X, (∑ k, (w k : ℂ) • (K k * X * (K k)ᴴ)) =
      (q : ℂ) • ∑ j, Matrix.diagonal (frameNat n · j) * X *
        (Matrix.diagonal (frameNat n · j))ᴴ := by
    intro X
    have h := heq X
    rw [frameChannel_action] at h
    simpa only [κ, K, w, Fintype.sum_sigma, Fintype.sum_prod_type,
      RandomizedProtocol.successfulMap, Protocol.successfulMap, Finset.smul_sum] using h
  have hidentity := frame_energy_identity n w K q hmap
  have htotal : (∑ k, w k * coefficientEnergy n (K k)) ≤
      4 * n * (4 : ℝ) ^ R := by
    calc
      _ = ∑ s, p.probability s *
          (∑ h, ∑ a, coefficientEnergy n ((p.tree s).krausFrom 1 h a)) := by
        simp only [κ, K, w, Fintype.sum_sigma, Fintype.sum_prod_type, Finset.mul_sum]
      _ ≤ ∑ s, p.probability s * (4 * n * (4 : ℝ) ^ R) := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : p.probability s = 0
        · simp only [hs, zero_mul, le_refl]
        · apply mul_le_mul_of_nonneg_left _ (p.nonnegative s)
          apply tree_energy_bound n hn
          intro h a
          exact exact_frame_span n w hw K q hmap ⟨s, h, a⟩
            (lt_of_le_of_ne (p.nonnegative s) (Ne.symm hs))
      _ = _ := by rw [← Finset.sum_mul, p.total, one_mul]
  rw [hidentity] at htotal
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith

theorem result : ¬ claim := by
  rintro ⟨R, q₀, hq₀, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 : ℝ) (4 * (4 : ℝ) ^ R / q₀))
  have hn₂ : 2 ≤ n := by exact_mod_cast (le_max_left _ _).trans hn.le
  obtain ⟨p, q, hq, heq⟩ := h (Fintype.card (FrameIndex n))
    (frameChannel n (by omega))
  have hb := simulation_bound n hn₂ p q heq
  have hlarge := (div_lt_iff₀ hq₀).mp ((le_max_right _ _).trans_lt hn)
  have hmul := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ n)
  nlinarith

#print axioms result

end D5.S3.Quantum.QuantumChannels.OneQubitAdaptiveSimulationRefutation
