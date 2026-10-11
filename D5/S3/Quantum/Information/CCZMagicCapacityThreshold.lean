/- GID: D5/S3/Quantum/Information/CCZMagicCapacityThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CCZMagicCapacityThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/CCZMagicCapacityThreshold.claim; result=D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result; claim=D5/S3/Quantum/Information/CCZMagicCapacityThreshold.claim
   digest: The noisy CCZ gate preserves magic with a reference at depolarizing strength 1/2. -/

/-
result: proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#15085; Refuted)
Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.depolarized (declaration statement_id sha256:24b644702cdd55fca7f15864e69044d03389fbf696780b679efb0e0478b51b69), used by depol and this module. Settling Freeze owner prerequisite: sha256:7e0df82ab5d6a661e6e797ade5a23cfbc0c3258e8c2ca14f7dcce4c3d2b0ed5b.
Private auxiliary theorems (all proof_shape: bind-only; consumers):
  q_upper_sound: diag_quadratic
  q_upper_as_full: IsQuad.exists_full
  IsQuad.exists_full: raw_overlap_bound, diag_quadratic
  diag_card: omega_pure
  omega_pure: result
  affine_card_dichotomy: raw_overlap_bound
  q3_sound: raw_overlap_bound
  full_certificate: full_sound
  phaseInt_sound: full_sound
  full_sound: raw_overlap_bound
  binEquiv_apply: support_card
  support_card: raw_overlap_bound, raw_norm2
  phase_norm: raw_overlap_bound, raw_norm2
  ccz_norm: raw_overlap_bound
  raw_overlap_bound: scaled_overlap_bound
  raw_norm2: scaled_overlap_bound
  norm2_smul: scaled_overlap_bound, diagonal_overlap_bound
  sqrt8_factor: scaled_overlap_bound, alpha_product
  raw_overlap: scaled_overlap_bound
  scaled_overlap_bound: overlap_bound
  overlap_bound: diagonal_overlap_bound
  diag_quadratic: diagonal_normal_form
  bin_diag: diag_phase, diagonal_raw
  diag_phase_certificate: diag_phase
  phase_as_I: diag_phase
  diag_phase: diagonal_raw
  diagonal_raw: diagonal_normal_form
  support_card_pos: raw_to_normal
  raw_to_normal: diagonal_normal_form
  diagonal_normal_form: diagonal_overlap_bound
  diagonal_overlap_bound: witness_nonneg
  sum_join: sum_diag
  join_diag: sum_diag
  sum_diag: witness_trace
  diag_left: witness_trace
  append_diagonal_inj: witness_trace
  witness_trace: witness_pure, witness_value
  witness_pure: witness_nonneg
  witness_nonneg: result
  witness_certificate: witness_value
  signQ_cast: psi_product, inputQ_sound
  alpha_product: psi_product, omega_outer
  psi_product: witness_value
  omega_outer: inputQ_sound
  gate_apply: inputQ_sound
  inputQ_sound: outputQ_sound
  depolAt_formula: noiseQ_sound
  noiseQ_sound: outputQ_sound
  outputQ_sound: witness_value
  witness_value: result
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
open scoped Classical
namespace D5.S3.Quantum.Information.CCZMagicCapacityThreshold
open Matrix Complex
open scoped BigOperators ComplexOrder
-- Ordered coefficients represent the same quadratic forms as upper triangular coefficients.
def qUpper {n : ℕ} (c : Fin n → Fin n → ZMod 2) (x : (Fin n → ZMod 2)) : ZMod 2 :=
  ∑ i, ∑ j, if i ≤ j then c i j * x i * x j else 0
def IsQuad {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ c : Fin n → Fin n → ZMod 2, q = qUpper c
def stabVec (n : ℕ) (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2)))
    (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (x : (Fin n → Bool)) : ℂ :=
  if (fun i => if x i then (1 : ZMod 2) else 0) ∈ K then ((Real.sqrt (((K : Set (Fin n → ZMod 2)).toFinset.card)) : ℂ))⁻¹ *
    Complex.I ^ (∑ i, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) * (-1) ^ (q ((fun i => if x i then (1 : ZMod 2) else 0))).val else 0
def IsPureStab (n : ℕ) (ρ : (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) : Prop :=
  ∃ (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2))) (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)),
    (K : Set ((Fin n → ZMod 2))).Nonempty ∧ IsQuad q ∧
    ρ = vecMulVec (stabVec n K q b) (star (stabVec n K q b))
def STAB (n : ℕ) : Set ((Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := convexHull ℝ {ρ | IsPureStab n ρ}
private def cczSign (x : (Fin 3 → Bool)) : ℂ := if x 0 && x 1 && x 2 then -1 else 1
def depol (lam : ℝ) (ρ : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  Matrix.reindex finTwoEquiv finTwoEquiv
    (D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized
      (d := 2) LinearMap.id lam
      (Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm ρ))
def depolAt (lam : ℝ) (j : Fin 6) (rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) := fun x y =>
  depol lam (fun u v => rho (Function.update x j u) (Function.update y j v)) (x j) (y j)
private lemma depol_formula (lam : ℝ) (rho : Matrix Bool Bool ℂ) :
    depol lam rho = (1-lam) • rho + (lam/2) • (trace rho • (1 : Matrix Bool Bool ℂ)) := by
  classical
  have htrace : (rho.submatrix finTwoEquiv finTwoEquiv).trace = rho.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp finTwoEquiv (fun b : Bool => rho b b)
  have hone (a b : Bool) :
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (finTwoEquiv.symm a) (finTwoEquiv.symm b) =
        (1 : Matrix Bool Bool ℂ) a b := by
    simp only [Matrix.one_apply]
    simp only [finTwoEquiv.symm.injective.eq_iff]
  ext a b
  simp [depol, Matrix.reindex_apply, Matrix.submatrix_apply,
    D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized,
    LinearMap.id_coe, Matrix.traceLinearMap_apply, htrace, hone]
def depolA (lam : ℝ) (ρ : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) :=
  depolAt lam 2 (depolAt lam 1 (depolAt lam 0 ρ))
def CCZ : (Matrix (Fin 3 → Bool) (Fin 3 → Bool) ℂ) := Matrix.diagonal cczSign
def CCZA : Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ :=
  Matrix.diagonal (fun x => CCZ (fun i => x (i.castAdd 3)) (fun i => x (i.castAdd 3)))
def chan (lam : ℝ) (ρ : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) := depolA lam (CCZA * ρ * CCZA)
def claim : Prop :=
  (∀ lam : ℝ, lam ∈ Set.Icc (1/3) 1 → ∀ ρ, IsPureStab 6 ρ → chan lam ρ ∈ STAB 6) ∧
  (∀ lam : ℝ, lam ∈ Set.Ico 0 (1/3) → ∃ ρ, IsPureStab 6 ρ ∧ chan lam ρ ∉ STAB 6)
private def Omega (x : (Fin 6 → Bool)) : ℂ :=
  if (∀ i : Fin 3, x (i.castAdd 3) = x (i.natAdd 3)) then ((Real.sqrt 8 : ℂ))⁻¹ else 0
private def psi (x : (Fin 3 → Bool)) : ℂ := ((Real.sqrt 8 : ℂ))⁻¹ * cczSign x
private lemma q_upper_sound {n : ℕ} (c : Fin n → Fin n → ZMod 2) (x : (Fin n → ZMod 2)) :
    (fun x => ∑ i, ∑ j, (c) i j * x i * x j) x = qUpper (fun i j => if i = j then c i j else c i j + c j i) x := by
  have hsplit : qUpper (fun i j => if i = j then c i j else c i j + c j i) x =
      (∑ i, ∑ j, if i ≤ j then c i j * x i * x j else 0) +
      (∑ i, ∑ j, if i < j then c j i * x j * x i else 0) := by
    unfold qUpper
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases h : i = j
    · subst j; simp
    · by_cases hij : i ≤ j
      · have hij' : i < j := lt_of_le_of_ne hij h
        simp [h,hij,hij']; ring
      · have hij' : ¬ i < j := by omega
        simp [h,hij,hij']
  rw [hsplit, Finset.sum_comm (f := fun i j => if i < j then c j i * x j * x i else 0)]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h : i ≤ j
  · have hj : ¬ j < i := not_lt_of_ge h; simp [h,hj]
  · have hj : j < i := lt_of_not_ge h; simp [h,hj]
private lemma q_upper_as_full {n : ℕ} (c : Fin n → Fin n → ZMod 2) :
    qUpper c = (fun x => ∑ i, ∑ j, ((fun i j => if i ≤ j then c i j else 0)) i j * x i * x j) := by
  ext x; simp only [qUpper]; congr 1; ext i; congr 1; ext j; split <;> simp
private lemma IsQuad.exists_full {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2} (hq : IsQuad q) :
    ∃ c : Fin n → Fin n → ZMod 2, q = (fun x => ∑ i, ∑ j, (c) i j * x i * x j) := by
  obtain ⟨c,rfl⟩ := hq
  exact ⟨_, q_upper_as_full c⟩
private def diagK : AffineSubspace (ZMod 2) ((Fin 6 → ZMod 2)) where
  carrier := {x | ∀ i : Fin 3, x (i.castAdd 3) = x (i.natAdd 3)}
  smul_vsub_vadd_mem' t p₁ p₂ p₃ h₁ h₂ h₃ := by
    intro i
    change t * (p₁ (i.castAdd 3) - p₂ (i.castAdd 3)) + p₃ (i.castAdd 3) =
      t * (p₁ (i.natAdd 3) - p₂ (i.natAdd 3)) + p₃ (i.natAdd 3)
    rw [h₁ i, h₂ i, h₃ i]
private def diagEquiv : (Fin 3 → ZMod 2) ≃ diagK where
  toFun x := ⟨Fin.append x x, by intro i; simp only [Fin.append_left, Fin.append_right]⟩
  invFun x i := x.val (i.castAdd 3)
  left_inv x := funext (Fin.append_left x x)
  right_inv x := by
    apply Subtype.ext
    ext i; fin_cases i
    · rfl
    · rfl
    · rfl
    · exact x.property 0
    · exact x.property 1
    · exact x.property 2
private lemma diag_card : ((diagK : Set (Fin 6 → ZMod 2)).toFinset.card) = 8 := by
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  change Nat.card diagK = 8
  rw [← Nat.card_congr diagEquiv]
  simp [Nat.card_fun]
private lemma omega_pure : IsPureStab 6 (vecMulVec Omega (star Omega)) := by
  refine ⟨diagK, fun _ => 0, 0, ⟨0, by intro i; rfl⟩, ⟨0, ?_⟩, ?_⟩
  · ext x; simp [qUpper]
  · have hv : stabVec 6 diagK (fun _ => 0) 0 = Omega := by
      ext x
      simp only [stabVec, Omega, diag_card]
      have hk : (fun i => if x i then (1 : ZMod 2) else 0) ∈ diagK ↔ ∀ i : Fin 3, x (i.castAdd 3) = x (i.natAdd 3) := by
        change (∀ i : Fin 3, ((fun i => if x i then (1 : ZMod 2) else 0)) (i.castAdd 3) = ((fun i => if x i then (1 : ZMod 2) else 0)) (i.natAdd 3)) ↔ _
        have eqbit (a b : Bool) : (if a then (1 : ZMod 2) else 0) = (if b then 1 else 0) ↔ a = b := by
          cases a <;> cases b <;> decide
        simp only [eqbit]
      simp [hk]
    rw [hv]
private lemma affine_card_dichotomy (K : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2)))
    (hK : (K : Set ((Fin 3 → ZMod 2))).Nonempty) : (K : Set (Fin 3 → ZMod 2)).toFinset.card ≤ 4 ∨ K = ⊤ := by
  let kCard := fun K : AffineSubspace (ZMod 2) (Fin 3 → ZMod 2) => (K : Set (Fin 3 → ZMod 2)).toFinset.card
  change kCard K ≤ 4 ∨ K = ⊤
  obtain ⟨p,hp⟩ := hK
  letI : Nonempty K := ⟨⟨p,hp⟩⟩
  have hcard : kCard K = 2 ^ Module.finrank (ZMod 2) K.direction := by
    dsimp only [kCard]
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    change Nat.card K = _
    rw [← Nat.card_congr (Equiv.vaddConst (⟨p,hp⟩ : K)),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : kCard K ≤ 8 := by
    change (K : Set ((Fin 3 → ZMod 2))).toFinset.card ≤ 8
    have h := Finset.card_le_card (Finset.subset_univ (K : Set ((Fin 3 → ZMod 2))).toFinset)
    simpa using h
  by_cases h : kCard K ≤ 4
  · exact Or.inl h
  · right
    have hc : kCard K = 8 := by
      have hd : Module.finrank (ZMod 2) K.direction ≤ 3 := by
        by_contra hn
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 4 ≤ Module.finrank (ZMod 2) K.direction by omega)
        rw [← hcard] at hh
        norm_num at hh
        omega
      interval_cases d : Module.finrank (ZMod 2) K.direction <;> norm_num [d] at hcard <;> omega
    apply SetLike.coe_injective
    change (K : Set ((Fin 3 → ZMod 2))) = Set.univ
    apply Set.toFinset_inj.mp
    apply Finset.eq_univ_of_card
    simpa [kCard] using hc
private def q3 (d : Fin 6 → ZMod 2) (x : (Fin 3 → ZMod 2)) : ZMod 2 :=
  d 0*x 0*x 0 + d 1*x 1*x 1 + d 2*x 2*x 2 +
  d 3*x 0*x 1 + d 4*x 0*x 2 + d 5*x 1*x 2
private def q3Data (c : Fin 3 → Fin 3 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![c 0 0,c 1 1,c 2 2,c 0 1+c 1 0,c 0 2+c 2 0,c 1 2+c 2 1]
private lemma q3_sound (c : Fin 3 → Fin 3 → ZMod 2) (x : (Fin 3 → ZMod 2)) :
    q3 (q3Data c) x = (fun x => ∑ i, ∑ j, (c) i j * x i * x j) x := by
  simp [q3, q3Data, Fin.sum_univ_succ]
  ring
private def phase (n : ℕ) (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (x : (Fin n → Bool)) : ℂ :=
  I ^ (∑ i, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) * (-1) ^ (q ((fun i => if x i then (1 : ZMod 2) else 0))).val
private def phaseInt (d : Fin 6 → ZMod 2) (b : (Fin 3 → ZMod 2)) (x : (Fin 3 → Bool)) : ℤ × ℤ :=
  let s : ℤ := (if x 0 && x 1 && x 2 then -1 else 1) *
    (if (q3 d ((fun i => if x i then (1 : ZMod 2) else 0))).val = 0 then 1 else -1)
  let e := (∑ i, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) % 4
  (s * (if e = 0 then 1 else if e = 2 then -1 else 0),
   s * (if e = 1 then 1 else if e = 3 then -1 else 0))
private def gauss (d : Fin 6 → ZMod 2) (b : (Fin 3 → ZMod 2)) : ℤ × ℤ :=
  (∑ x : (Fin 3 → Bool), (phaseInt d b x).1, ∑ x : (Fin 3 → Bool), (phaseInt d b x).2)
-- 64 quadratic coefficient strings and 8 linear phase strings.
private theorem full_certificate : ∀ (d : Fin 6 → ZMod 2) (b : (Fin 3 → ZMod 2)),
    (gauss d b).1^2 + (gauss d b).2^2 ≤ 36 := by
  decide +kernel
private lemma phaseInt_sound (d : Fin 6 → ZMod 2) (b : (Fin 3 → ZMod 2)) (x : (Fin 3 → Bool)) :
    cczSign x * phase 3 (q3 d) b x =
      ((phaseInt d b x).1 : ℂ) + ((phaseInt d b x).2 : ℂ) * I := by
  unfold phase
  rw [I_pow_eq_pow_mod]
  have he : (∑ i : Fin 3, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hq : (q3 d ((fun i => if x i then (1 : ZMod 2) else 0))).val = 0 ∨ (q3 d ((fun i => if x i then (1 : ZMod 2) else 0))).val = 1 := by
    have ht : (q3 d ((fun i => if x i then (1 : ZMod 2) else 0))).val < 2 := (q3 d ((fun i => if x i then (1 : ZMod 2) else 0))).isLt
    omega
  interval_cases e : (∑ i : Fin 3, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) % 4 <;>
    rcases hq with h | h <;>
    simp [phaseInt, e, h, cczSign]
private lemma full_sound (d : Fin 6 → ZMod 2) (b : (Fin 3 → ZMod 2)) :
    normSq (∑ x : (Fin 3 → Bool), cczSign x * phase 3 (q3 d) b x) ≤ 36 := by
  have he : (∑ x : (Fin 3 → Bool), cczSign x * phase 3 (q3 d) b x) =
      ((gauss d b).1 : ℂ) + ((gauss d b).2 : ℂ) * I := by
    simp_rw [phaseInt_sound]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Int.cast_sum, gauss]
  rw [he]
  have ht := full_certificate d b
  simpa [normSq, Complex.ext_iff, Complex.mul_re, Complex.mul_im, sq] using
    (show ((gauss d b).1 : ℝ)^2 + ((gauss d b).2 : ℝ)^2 ≤ 36 by exact_mod_cast ht)
private lemma binEquiv_apply {n : ℕ} (x : (Fin n → Bool)) : (Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv)) x = (fun i => if x i then (1 : ZMod 2) else 0) := by
  ext i
  change (finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv) (x i) = (if x i then (1 : ZMod 2) else 0)
  cases x i <;> rfl
private def support {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2))) : Finset ((Fin n → Bool)) :=
  Finset.univ.filter fun x => (fun i => if x i then (1 : ZMod 2) else 0) ∈ K
private lemma support_card {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2))) :
    (support K).card = ((K : Set (Fin n → ZMod 2)).toFinset.card) := by
  have he : (support K).image ((Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv))) = (K : Set ((Fin n → ZMod 2))).toFinset := by
    ext x
    simp only [Finset.mem_image, support, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, binEquiv_apply]
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx
      refine ⟨((Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv))).symm x, ?_, ?_⟩
      · rw [← binEquiv_apply, Equiv.apply_symm_apply]; exact hx
      · rw [← binEquiv_apply, Equiv.apply_symm_apply]
  rw [← he, Finset.card_image_of_injective _ ((Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv))).injective]
private lemma phase_norm (n : ℕ) (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (x : (Fin n → Bool)) :
    ‖phase n q b x‖ = 1 := by
  simp [phase,norm_mul,norm_pow]
private lemma ccz_norm (x : (Fin 3 → Bool)) : ‖cczSign x‖ = 1 := by
  simp [cczSign]; split <;> simp
private lemma raw_overlap_bound (K : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2)))
    (q : (Fin 3 → ZMod 2) → ZMod 2) (b : (Fin 3 → ZMod 2)) (hK : (K : Set ((Fin 3 → ZMod 2))).Nonempty)
    (hq : IsQuad q) :
    normSq (∑ x ∈ support K, cczSign x * phase 3 q b x) ≤ (9/2 : ℝ) * ((K : Set (Fin 3 → ZMod 2)).toFinset.card) := by
  rcases affine_card_dichotomy K hK with hk | rfl
  · have hh := norm_sum_le (support K) (fun x => cczSign x * phase 3 q b x)
    simp only [norm_mul,ccz_norm,phase_norm,one_mul,Finset.sum_const, nsmul_eq_mul,
      mul_one,support_card] at hh
    rw [normSq_eq_norm_sq]
    have hm : (((K : Set (Fin 3 → ZMod 2)).toFinset.card) : ℝ) ≤ 4 := by exact_mod_cast hk
    have h0 : 0 ≤ ‖∑ x ∈ support K, cczSign x * phase 3 q b x‖ := norm_nonneg _
    have h1 : 0 ≤ (((K : Set (Fin 3 → ZMod 2)).toFinset.card) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨c,rfl⟩ := hq.exists_full
    have h := full_sound (q3Data c) b
    have hqfun : q3 (q3Data c) = (fun x => ∑ i, ∑ j, (c) i j * x i * x j) := funext (q3_sound c)
    rw [hqfun] at h
    norm_num [support]
    exact h
private def rawVec {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2)))
    (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (x : (Fin n → Bool)) : ℂ :=
  if (fun i => if x i then (1 : ZMod 2) else 0) ∈ K then phase n q b x else 0
private lemma raw_norm2 {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2)))
    (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) : (∑ x, normSq (((rawVec K q b)) x)) = ((K : Set (Fin n → ZMod 2)).toFinset.card) := by
  have hp (x : (Fin n → Bool)) : normSq (phase n q b x) = 1 := by
    rw [normSq_eq_norm_sq,phase_norm]; norm_num
  simp only [rawVec,apply_ite,normSq_zero,hp]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,support,← support_card]
private lemma norm2_smul {n : ℕ} (a : ℂ) (v : ((Fin n → Bool) → ℂ)) :
    (∑ x, normSq (((a • v)) x)) = normSq a * (∑ x, normSq ((v) x)) := by
  simp [Pi.smul_apply,smul_eq_mul,normSq_mul,Finset.mul_sum]
private lemma sqrt8_factor : normSq (((Real.sqrt 8 : ℂ))⁻¹) = (1/8 : ℝ) := by
  rw [← Complex.ofReal_inv, Complex.normSq_ofReal]
  have hs : (Real.sqrt 8)^2 = 8 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 8 ≠ 0 := by positivity
  field_simp
  nlinarith
private lemma raw_overlap (K : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2)))
    (q : (Fin 3 → ZMod 2) → ZMod 2) (b : (Fin 3 → ZMod 2)) :
    (dotProduct (star psi) (rawVec K q b)) = ((Real.sqrt 8 : ℂ))⁻¹ *
      (∑ x ∈ support K, cczSign x * phase 3 q b x) := by
  have hs (x : (Fin 3 → Bool)) : star (cczSign x) = cczSign x := by
    simp [cczSign]; split <;> simp
  simp only [dotProduct,Pi.star_apply,psi,star_mul,star_inv,Complex.star_def,Complex.conj_ofReal,
    hs, rawVec,Finset.mul_sum]
  rw [support, Finset.sum_filter]
  congr 1; ext x
  split <;> simp [mul_assoc,mul_comm,mul_left_comm]
private lemma scaled_overlap_bound (K : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2)))
    (q : (Fin 3 → ZMod 2) → ZMod 2) (b : (Fin 3 → ZMod 2)) (hK : (K : Set ((Fin 3 → ZMod 2))).Nonempty)
    (hq : IsQuad q) (a : ℂ) :
    normSq ((dotProduct (star psi) (a • rawVec K q b))) ≤ (9/16 : ℝ) * (∑ x, normSq (((a • rawVec K q b)) x)) := by
  rw [dotProduct_smul, smul_eq_mul,normSq_mul,raw_overlap,normSq_mul,sqrt8_factor,norm2_smul,raw_norm2]
  have h := raw_overlap_bound K q b hK hq
  have h0 := normSq_nonneg a
  nlinarith [mul_le_mul_of_nonneg_left h h0]
private lemma overlap_bound (K : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2)))
    (q : (Fin 3 → ZMod 2) → ZMod 2) (b : (Fin 3 → ZMod 2)) (hK : (K : Set ((Fin 3 → ZMod 2))).Nonempty)
    (hq : IsQuad q) :
    normSq ((dotProduct (star psi) (stabVec 3 K q b))) ≤ (9/16 : ℝ) * (∑ x, normSq (((stabVec 3 K q b)) x)) := by
  have he : stabVec 3 K q b = ((Real.sqrt (((K : Set (Fin 3 → ZMod 2)).toFinset.card)) : ℂ))⁻¹ • rawVec K q b := by
    ext x; simp [stabVec,rawVec,phase,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [he]; exact scaled_overlap_bound K q b hK hq _
private def diagLin : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.pi (fun i => LinearMap.proj (Fin.append (id : Fin 3 → Fin 3) id i))
private def diagB (b : (Fin 6 → ZMod 2)) : (Fin 3 → ZMod 2) := fun i => b (i.castAdd 3) + b (i.natAdd 3)
private def diagQ (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) (x : (Fin 3 → ZMod 2)) : ZMod 2 :=
  q (diagLin x) + ∑ i, b (i.castAdd 3) * b (i.natAdd 3) * x i * x i
private def diagC (c : Fin 6 → Fin 6 → ZMod 2) (b : (Fin 6 → ZMod 2)) : Fin 3 → Fin 3 → ZMod 2 :=
  fun i j => c (i.castAdd 3) (j.castAdd 3) + c (i.castAdd 3) (j.natAdd 3) +
    c (i.natAdd 3) (j.castAdd 3) + c (i.natAdd 3) (j.natAdd 3) +
    (if i = j then b (i.castAdd 3) * b (i.natAdd 3) else 0)
private lemma diag_quadratic (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) (hq : IsQuad q) :
    IsQuad (diagQ q b) := by
  obtain ⟨c,rfl⟩ := hq.exists_full
  refine ⟨(fun i j => if i = j then diagC c b i j else diagC c b i j + diagC c b j i), ?_⟩
  ext x
  rw [← q_upper_sound]
  simp [diagQ,diagC,diagLin,Fin.append,Fin.addCases,Fin.sum_univ_succ]
  ring
private lemma bin_diag (x : (Fin 3 → Bool)) : (fun i => if (Fin.append (m := 3) (n := 3) x x) i then (1 : ZMod 2) else 0) = diagLin ((fun i => if x i then (1 : ZMod 2) else 0)) := by
  ext i; fin_cases i <;> rfl
-- This is an equality of integer exponents modulo four, not a complex native check.
private lemma diag_phase_certificate : ∀ (b : (Fin 6 → ZMod 2)) (x : (Fin 3 → ZMod 2)) (qv : ZMod 2),
    ((∑ i : Fin 6, (b i).val * (diagLin x i).val) + 2*qv.val) % 4 =
    ((∑ i : Fin 3, (diagB b i).val * (x i).val) +
      2*(qv + ∑ i : Fin 3, b (i.castAdd 3)*b (i.natAdd 3)*x i*x i).val) % 4 := by
  decide +kernel
private lemma phase_as_I {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (x : (Fin n → Bool)) :
    phase n q b x = I ^ ((∑ i, (b i).val * (((fun i => if x i then (1 : ZMod 2) else 0)) i).val) + 2*(q ((fun i => if x i then (1 : ZMod 2) else 0))).val) := by
  simp only [phase, ← I_sq, ← pow_mul, ← pow_add]
private lemma diag_phase (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) (x : (Fin 3 → Bool)) :
    phase 6 q b ((Fin.append (m := 3) (n := 3) x x)) = phase 3 (diagQ q b) (diagB b) x := by
  rw [phase_as_I,phase_as_I]
  conv_lhs => rw [I_pow_eq_pow_mod]
  conv_rhs => rw [I_pow_eq_pow_mod]
  rw [bin_diag]
  congr 1
  exact diag_phase_certificate b ((fun i => if x i then (1 : ZMod 2) else 0)) (q (diagLin ((fun i => if x i then (1 : ZMod 2) else 0))))
private lemma diagonal_raw (K : AffineSubspace (ZMod 2) ((Fin 6 → ZMod 2)))
    (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) :
    (fun x => stabVec 6 K q b ((Fin.append (m := 3) (n := 3) x x))) =
      ((Real.sqrt (((K : Set (Fin 6 → ZMod 2)).toFinset.card)) : ℂ))⁻¹ • rawVec ((K.comap diagLin.toAffineMap)) (diagQ q b) (diagB b) := by
  ext x
  have hk : (fun i => if (Fin.append (m := 3) (n := 3) x x) i then (1 : ZMod 2) else 0) ∈ K ↔ (fun i => if x i then (1 : ZMod 2) else 0) ∈ (K.comap diagLin.toAffineMap) := by
    change (fun i => if (Fin.append (m := 3) (n := 3) x x) i then (1 : ZMod 2) else 0) ∈ K ↔ diagLin ((fun i => if x i then (1 : ZMod 2) else 0)) ∈ K
    rw [bin_diag]
  have hv : stabVec 6 K q b = ((Real.sqrt (((K : Set (Fin 6 → ZMod 2)).toFinset.card)) : ℂ))⁻¹ • rawVec K q b := by
    ext y; simp [stabVec,rawVec,phase,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [hv]
  simp [hk,diag_phase,rawVec,Pi.smul_apply,smul_eq_mul]
private lemma support_card_pos {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2)))
    (hK : (K : Set ((Fin n → ZMod 2))).Nonempty) : 0 < ((K : Set (Fin n → ZMod 2)).toFinset.card) := by
  rw [Finset.card_pos,Set.toFinset_nonempty]; exact hK
private lemma raw_to_normal {n : ℕ} (K : AffineSubspace (ZMod 2) ((Fin n → ZMod 2)))
    (q : (Fin n → ZMod 2) → ZMod 2) (b : (Fin n → ZMod 2)) (hK : (K : Set ((Fin n → ZMod 2))).Nonempty) :
    rawVec K q b = (Real.sqrt (((K : Set (Fin n → ZMod 2)).toFinset.card)) : ℂ) • stabVec n K q b := by
  have hr : (Real.sqrt (((K : Set (Fin n → ZMod 2)).toFinset.card)) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (((K : Set (Fin n → ZMod 2)).toFinset.card)) ≠ 0 from ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast support_card_pos K hK)))
  ext x
  simp only [rawVec,stabVec,Pi.smul_apply,smul_eq_mul,phase]
  split <;> simp only [mul_assoc, mul_inv_cancel_left₀ hr, smul_eq_mul, mul_zero]
private lemma diagonal_normal_form (K : AffineSubspace (ZMod 2) ((Fin 6 → ZMod 2)))
    (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) (hq : IsQuad q) :
    (∃ (K' : AffineSubspace (ZMod 2) ((Fin 3 → ZMod 2))) (q' : (Fin 3 → ZMod 2) → ZMod 2)
      (b' : (Fin 3 → ZMod 2)) (a : ℂ), (K' : Set ((Fin 3 → ZMod 2))).Nonempty ∧ IsQuad q' ∧
      (fun x => stabVec 6 K q b ((Fin.append (m := 3) (n := 3) x x))) = a • stabVec 3 K' q' b') ∨
      (fun x => stabVec 6 K q b ((Fin.append (m := 3) (n := 3) x x))) = 0 := by
  rw [diagonal_raw]
  by_cases h : ((K.comap diagLin.toAffineMap) : Set ((Fin 3 → ZMod 2))).Nonempty
  · left
    refine ⟨(K.comap diagLin.toAffineMap),diagQ q b,diagB b,
      ((Real.sqrt (((K : Set (Fin 6 → ZMod 2)).toFinset.card)) : ℂ))⁻¹ * (Real.sqrt (((K.comap diagLin.toAffineMap : Set (Fin 3 → ZMod 2)).toFinset.card)) : ℂ),
      h,diag_quadratic q b hq,?_⟩
    rw [raw_to_normal _ _ _ h,smul_smul]
  · right
    have hz : rawVec ((K.comap diagLin.toAffineMap)) (diagQ q b) (diagB b) = 0 := by
      ext x
      have hx : (fun i => if x i then (1 : ZMod 2) else 0) ∉ (K.comap diagLin.toAffineMap) := fun hx => h ⟨(fun i => if x i then (1 : ZMod 2) else 0),hx⟩
      simp [rawVec,hx]
    simp [hz]
private lemma diagonal_overlap_bound (K : AffineSubspace (ZMod 2) ((Fin 6 → ZMod 2)))
    (q : (Fin 6 → ZMod 2) → ZMod 2) (b : (Fin 6 → ZMod 2)) (hq : IsQuad q) :
    normSq ((dotProduct (star psi) (fun x => stabVec 6 K q b ((Fin.append (m := 3) (n := 3) x x))))) ≤
      (9/16 : ℝ) * (∑ x, normSq (((fun x => stabVec 6 K q b ((Fin.append (m := 3) (n := 3) x x)))) x)) := by
  rcases diagonal_normal_form K q b hq with ⟨K',q',b',a,hK',hq',he⟩ | hz
  · rw [he,dotProduct_smul,smul_eq_mul,normSq_mul,norm2_smul]
    have h := mul_le_mul_of_nonneg_left (overlap_bound K' q' b' hK' hq') (normSq_nonneg a)
    nlinarith
  · rw [hz]; simp [dotProduct,Pi.star_apply]
private def replaceAt (j : Fin 6) (ρ : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) := fun x y =>
  if x j = y j then (1/2 : ℂ) * ∑ t : Bool,
    ρ (Function.update x j t) (Function.update y j t) else 0
private def W : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) := fun x y =>
  if (∀ i : Fin 3, x (i.castAdd 3) = x (i.natAdd 3)) ∧
     (∀ i : Fin 3, y (i.castAdd 3) = y (i.natAdd 3)) then
    (if x = y then (9/16 : ℂ) else 0) -
    psi (fun i => x (i.castAdd 3)) * star (psi (fun i => y (i.castAdd 3))) else 0

private lemma sum_join {M : Type*} [AddCommMonoid M] (f : (Fin 6 → Bool) → M) :
    (∑ x, f x) = ∑ a : (Fin 3 → Bool), ∑ b : (Fin 3 → Bool), f (Fin.append a b) := by
  have he : (∑ x, f x) = ∑ p : (Fin 3 → Bool) × (Fin 3 → Bool), f (Fin.append p.1 p.2) := by
    apply Fintype.sum_equiv ((Equiv.arrowCongr ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm) (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin 3) Bool))
    intro x
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [he,Fintype.sum_prod_type]
@[simp]
private lemma join_diag (a b : (Fin 3 → Bool)) :
    (∀ i : Fin 3, Fin.append a b (i.castAdd 3) = Fin.append a b (i.addNat 3)) ↔ a = b := by
  have he (i : Fin 3) : i.addNat 3 = Fin.natAdd 3 i := by
    ext; simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
  simp only [he, Fin.append_left,Fin.append_right]; exact funext_iff.symm
private lemma sum_diag {M : Type*} [AddCommMonoid M] (f : (Fin 6 → Bool) → M) :
    (∑ x : (Fin 6 → Bool), if (∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)) then f x else 0) =
    ∑ a : (Fin 3 → Bool), f ((Fin.append (m := 3) (n := 3) a a)) := by
  rw [sum_join]
  simp only [join_diag,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
@[simp]
private lemma diag_left (a : (Fin 3 → Bool)) : (fun i : Fin 3 => (Fin.append (m := 3) (n := 3) a a) (i.castAdd 3)) = a := by
  exact funext (Fin.append_left a a)
@[simp]
private lemma append_diagonal_inj (a b : (Fin 3 → Bool)) : (Fin.append (m := 3) (n := 3) a a) = (Fin.append (m := 3) (n := 3) b b) ↔ a = b := by
  constructor
  · intro h; have := congrArg (fun x : (Fin 6 → Bool) => fun i : Fin 3 => x (i.castAdd 3)) h
    simpa using this
  · intro h; rw [h]
private lemma witness_trace (rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) :
    trace (W * rho) = ∑ a : (Fin 3 → Bool), ∑ b : (Fin 3 → Bool),
      ((if a = b then (9/16 : ℂ) else 0) - psi a * star (psi b)) * rho ((Fin.append (m := 3) (n := 3) b b)) ((Fin.append (m := 3) (n := 3) a a)) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  have hi (x : (Fin 6 → Bool)) : (∑ y : (Fin 6 → Bool), W x y * rho y x) =
      if (∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)) then
        ∑ y : (Fin 6 → Bool), if (∀ i : Fin 3, y (i.castAdd 3) = y (i.addNat 3)) then
          ((if x = y then (9/16 : ℂ) else 0) -
            psi (fun i => x (i.castAdd 3)) * star (psi (fun i => y (i.castAdd 3)))) * rho y x else 0
      else 0 := by
    by_cases hx : ∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)
    · rw [if_pos hx]
      apply Finset.sum_congr rfl; intro y _
      simp only [W, Fin.natAdd,Fin.addNat,Nat.add_comm] at *
      by_cases hy : ∀ i : Fin 3, y (i.castAdd 3) = y (i.addNat 3)
      · simp only [Fin.addNat] at hy
        rw [if_pos ⟨hx,hy⟩,if_pos hy]
      · simp only [Fin.addNat] at hy
        rw [if_neg (fun h => hy h.2),if_neg hy,zero_mul]
    · rw [if_neg hx]
      apply Finset.sum_eq_zero; intro y _
      simp only [W, Fin.natAdd,Fin.addNat,Nat.add_comm] at *
      rw [if_neg (fun h => hx h.1),zero_mul]
  simp_rw [hi]
  rw [sum_diag]
  simp_rw [sum_diag,append_diagonal_inj,diag_left]
private lemma witness_pure (phi : ((Fin 6 → Bool) → ℂ)) :
    trace (W * vecMulVec phi (star phi)) =
      (((9/16 : ℝ) * (∑ x, normSq (((fun x => phi ((Fin.append (m := 3) (n := 3) x x)))) x)) -
        normSq ((dotProduct (star psi) (fun x => phi ((Fin.append (m := 3) (n := 3) x x)))))) : ℂ) := by
  rw [witness_trace]
  simp only [vecMulVec_apply,Pi.star_apply,sub_mul,Finset.sum_sub_distrib]
  let xi : ((Fin 3 → Bool) → ℂ) := fun x => phi ((Fin.append (m := 3) (n := 3) x x))
  have hd : (∑ a : (Fin 3 → Bool), ∑ b : (Fin 3 → Bool),
      (if a = b then (9/16 : ℂ) else 0) * (xi b * star (xi a))) =
      (9/16 : ℂ) * ((∑ x, normSq ((xi) x)) : ℂ) := by
    simp only [ite_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,
      Complex.star_def,Finset.mul_sum]
    congr 1; ext x; ring
  have hp : (∑ a : (Fin 3 → Bool), ∑ b : (Fin 3 → Bool),
      (psi a * star (psi b)) * (xi b * star (xi a))) = (normSq ((dotProduct (star psi) xi)) : ℂ) := by
    rw [← Complex.mul_conj]
    simp only [dotProduct,Pi.star_apply,Complex.star_def,map_sum,map_mul,Complex.conj_conj,
      Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  change _ - _ = _
  rw [hd,hp]
  norm_num only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  simp only [Complex.ofReal_sum]
  rfl
private lemma witness_nonneg (rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) (hrho : rho ∈ STAB 6) : 0 ≤ trace (W * rho) := by
  apply convexHull_min (t := {rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ) | 0 ≤ trace (W * rho)}) ?_ ?_ hrho
  · rintro sigma ⟨K,q,b,hK,hq,rfl⟩
    change 0 ≤ trace (W * vecMulVec (stabVec 6 K q b) (star (stabVec 6 K q b)))
    rw [witness_pure]
    rw [← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.zero_le_real]
    have h := diagonal_overlap_bound K q b hq
    linarith
  · intro x hx y hy a b ha hb hab
    change 0 ≤ trace (W * (a • x + b • y))
    have he : trace (W * (a • x + b • y)) = a • trace (W * x) + b • trace (W * y) := by
      simp [Matrix.mul_add]
    rw [he]
    exact add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)
private def signQ (a : (Fin 3 → Bool)) : ℚ := if a 0 && a 1 && a 2 then -1 else 1
private def inputQ : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ := fun x y =>
  if (∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)) ∧
     (∀ i : Fin 3, y (i.castAdd 3) = y (i.addNat 3)) then
    signQ (fun i => x (i.castAdd 3)) * signQ (fun i => y (i.castAdd 3)) / 8 else 0
private def replaceQ (j : Fin 6) (rho : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ) : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ :=
  fun x y => if x j = y j then (1/2 : ℚ) * ∑ t : Bool,
    rho (Function.update x j t) (Function.update y j t) else 0
private def noiseQ (j : Fin 6) (rho : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ) : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ :=
  (1/2 : ℚ) • rho + (1/2 : ℚ) • replaceQ j rho
private def outputQ : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ := noiseQ 2 (noiseQ 1 (noiseQ 0 inputQ))
private def coreQ (a b : (Fin 3 → Bool)) : ℚ :=
  (if a = b then (9/16 : ℚ) else 0) - signQ a * signQ b / 8
private lemma witness_certificate : (∑ a : (Fin 3 → Bool), ∑ b : (Fin 3 → Bool),
    coreQ a b * outputQ ((Fin.append (m := 3) (n := 3) b b)) ((Fin.append (m := 3) (n := 3) a a))) = (-7/1024 : ℚ) := by
  decide +kernel
private lemma signQ_cast (a : (Fin 3 → Bool)) : (signQ a : ℂ) = cczSign a := by
  unfold signQ cczSign; split <;> norm_num
private lemma alpha_product : ((Real.sqrt 8 : ℂ))⁻¹ * star (((Real.sqrt 8 : ℂ))⁻¹) = (1/8 : ℂ) := by
  have h := congrArg Complex.ofReal sqrt8_factor
  simpa only [Complex.normSq_eq_conj_mul_self,Complex.star_def,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,mul_comm] using h
private lemma psi_product (a b : (Fin 3 → Bool)) : psi a * star (psi b) = (signQ a * signQ b / 8 : ℚ) := by
  have hs (x : (Fin 3 → Bool)) : star (cczSign x) = cczSign x := by
    simp [cczSign]; split <;> simp
  simp only [psi,star_mul,hs,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,signQ_cast]
  calc
    _ = (((Real.sqrt 8 : ℂ))⁻¹ * star (((Real.sqrt 8 : ℂ))⁻¹)) * (cczSign a * cczSign b) := by ring
    _ = _ := by rw [alpha_product]; ring
private lemma omega_outer (x y : (Fin 6 → Bool)) : vecMulVec Omega (star Omega) x y =
    if (∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)) ∧
       (∀ i : Fin 3, y (i.castAdd 3) = y (i.addNat 3)) then (1/8 : ℂ) else 0 := by
  by_cases hx : ∀ i : Fin 3, x (i.castAdd 3) = x (i.addNat 3)
  all_goals by_cases hy : ∀ i : Fin 3, y (i.castAdd 3) = y (i.addNat 3)
  all_goals simp only [vecMulVec_apply,Pi.star_apply,Omega,Fin.natAdd,Fin.addNat,Nat.add_comm] at *
  all_goals simp only [hx,hy,forall_const,
    and_true,and_false,true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,star_zero]
  exact alpha_product
private lemma gate_apply (rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) (x y : (Fin 6 → Bool)) : (CCZA * rho * CCZA) x y =
    cczSign (fun i => x (i.castAdd 3)) * rho x y * cczSign (fun i => y (i.castAdd 3)) := by
  have hd : CCZA = Matrix.diagonal (fun x : (Fin 6 → Bool) => cczSign (fun i => x (i.castAdd 3))) := by
    ext a b; simp [CCZA,CCZ,Matrix.diagonal_apply]
  rw [hd,Matrix.mul_diagonal,Matrix.diagonal_mul]
private lemma inputQ_sound : CCZA * vecMulVec Omega (star Omega) * CCZA = inputQ.map (Rat.castHom ℂ) := by
  ext x y
  rw [gate_apply,omega_outer]
  simp only [Matrix.map_apply,Rat.castHom,inputQ]
  split <;> simp [Rat.cast_div,Rat.cast_mul,signQ_cast] <;> ring
private lemma depolAt_formula (lam : ℝ) (j : Fin 6) (rho : (Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ)) :
    depolAt lam j rho = (1-lam) • rho + lam • replaceAt j rho := by
  ext x y
  simp only [depolAt]
  let block : Matrix Bool Bool ℂ := fun u v =>
    rho (Function.update x j u) (Function.update y j v)
  change (depol lam block) (x j) (y j) = _
  rw [depol_formula lam block]
  change (1-lam : ℝ) • rho (Function.update x j (x j)) (Function.update y j (y j)) +
    (lam/2 : ℝ) • ((∑ t : Bool, rho (Function.update x j t) (Function.update y j t)) *
      (if x j = y j then (1 : ℂ) else 0)) =
    (1-lam : ℝ) • rho x y + lam •
      (if x j = y j then (1/2 : ℂ) * ∑ t : Bool,
        rho (Function.update x j t) (Function.update y j t) else 0)
  rw [Function.update_eq_self,Function.update_eq_self]
  by_cases h : x j = y j
  · rw [if_pos h,if_pos h]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_ofNat,mul_one]
    ring
  · rw [if_neg h,if_neg h]
    simp
private lemma noiseQ_sound (j : Fin 6) (rho : Matrix ((Fin 6 → Bool)) ((Fin 6 → Bool)) ℚ) :
    depolAt (1/2) j (rho.map (Rat.castHom ℂ)) = (noiseQ j rho).map (Rat.castHom ℂ) := by
  rw [depolAt_formula]
  ext x y
  norm_num [replaceAt,noiseQ,replaceQ,Matrix.map_apply,Matrix.add_apply,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Rat.castHom,Rat.cast_add,
    Rat.cast_mul,Rat.cast_div,Rat.cast_sum,Complex.real_smul]
  split <;> simp [Rat.cast_sum]
private lemma outputQ_sound : chan (1/2) (vecMulVec Omega (star Omega)) = outputQ.map (Rat.castHom ℂ) := by
  unfold chan depolA
  rw [inputQ_sound,noiseQ_sound,noiseQ_sound,noiseQ_sound]
  rfl
private lemma witness_value : trace (W * chan (1/2) (vecMulVec Omega (star Omega))) = (-7/1024 : ℂ) := by
  rw [witness_trace,outputQ_sound]
  have hterm (a b : (Fin 3 → Bool)) :
      ((if a = b then (9/16 : ℂ) else 0) - psi a * star (psi b)) *
        outputQ.map (Rat.castHom ℂ) ((Fin.append (m := 3) (n := 3) b b)) ((Fin.append (m := 3) (n := 3) a a)) =
      ((coreQ a b * outputQ ((Fin.append (m := 3) (n := 3) b b)) ((Fin.append (m := 3) (n := 3) a a)) : ℚ) : ℂ) := by
    rw [psi_product]
    simp [coreQ,Rat.cast_sub,Rat.cast_mul]
    split <;> norm_num
  simp_rw [hterm]
  have h := congrArg (fun r : ℚ => (r : ℂ)) witness_certificate
  simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] using h
theorem result : ¬ claim := by
  intro h
  have hs := h.1 (1/2) (by norm_num : (1/2 : ℝ) ∈ Set.Icc (1/3) 1)
    (vecMulVec Omega (star Omega)) omega_pure
  have hw := witness_nonneg _ hs
  rw [witness_value] at hw
  norm_num [Complex.le_def] at hw



end D5.S3.Quantum.Information.CCZMagicCapacityThreshold
