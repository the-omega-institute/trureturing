/- GID: D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl
   generality: G
   mirror-B: D5/B/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: none
   digest: Two-copy Haar invariants yield the exact two-site identity/swap rule. -/

/-
proof_shape: unitaryCompactSpace: bind-only; consumer: haar_probability.
proof_shape: unitaryBorelSpace: bind-only; consumer: haar_probability.
proof_shape: haar_probability: bind-only; consumer: haarAverage_idempotent.
proof_shape: haarAverage_hermitian: bind-only; consumer: gate_mixed_rule.
proof_shape: haarAverage_idempotent: bind-only; consumer: layer_idempotent in the PB host.
proof_shape: localPermutation_gram: bind-only; consumer: gate_mixed_rule.
proof_shape: local_identity_fixed: bind-only; consumer: gate_mixed_rule.
proof_shape: local_swap_fixed: bind-only; consumer: gate_mixed_rule.
proof_shape: gate_mixed_rule: content.
proof_shape: haarAverage_identity_fixed: bind-only; consumer: twirlTrace.
proof_shape: haarAverage_swap_fixed: bind-only; consumer: twirlSwapTrace.
proof_shape: haarAverage_image_span: bind-only; consumer: twirlFormula.
proof_shape: hermitian_fixed_pairing: bind-only; consumer: twirlTrace.
proof_shape: swapHermitian: bind-only; consumers: twirlSwapTrace, WernerTesterIncompleteness.flip_facts.
proof_shape: swapSquare: bind-only; consumers: twirlFormula, WernerTesterIncompleteness.flip_facts.
proof_shape: traceSwap: bind-only; consumers: twirlFormula, WernerTesterIncompleteness.
proof_shape: twirlTrace: bind-only; consumer: twirlFormula.
proof_shape: twirlSwapTrace: bind-only; consumer: twirlFormula.
proof_shape: twirlFormula: bind-only; consumers: pure_twirl, CHaarConcatenationNonmonotone.haarAverageEntry.
proof_shape: literalMoment_integrable: bind-only; consumer: CHaarConcatenationNonmonotone.momentOp2HaarEntries.
proof_shape: literalMoment_vectorize: bind-only; consumer: haarAverage_identity_fixed.
proof_shape: Commutant.replicaSwap_apply: bind-only; consumer: CHaarConcatenationNonmonotone.moment22Reindex.
escape_witness: Commutant.two_copy_commutant, via quarter phases and a Hadamard constraint.
admission_basis: escape-witness
Direct frozen dependencies: none; the upstream imports are pinned Mathlib.
Escape audit unfinished for hadamard_unitary: https://github.com/the-omega-institute/trureturing/issues/16609.
The finite Gram and coefficient identities are consumed normalization helpers. The new
content is a universal commutant classification and the literal Haar-average reduction;
no bounded enumeration, checker, numerical certificate or positive finite instance is retained.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open Matrix MeasureTheory TopologicalSpace
open scoped Kronecker ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

variable {n : Type*} [Fintype n] [DecidableEq n]

instance unitaryCompactSpace : CompactSpace (Matrix.unitaryGroup n ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_unitary (R := Matrix n n ℂ)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix n n ℂ)) (r := 1)).subset
    intro U hU
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
    exact entry_norm_bound_of_unitary hU

instance unitaryMeasurableSpace : MeasurableSpace (Matrix.unitaryGroup n ℂ) :=
  borel _

instance unitaryBorelSpace : BorelSpace (Matrix.unitaryGroup n ℂ) := ⟨rfl⟩

instance haar_probability : IsProbabilityMeasure
    (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))) :=
  ⟨Measure.haarMeasure_self⟩

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
def permutationUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (e : Equiv.Perm n) : Matrix.unitaryGroup n ℂ :=
  ⟨e.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff]
    simp [Matrix.star_eq_conjTranspose,← Matrix.permMatrix_mul]⟩

def literalMoment {I : Type*} (U : Matrix I I ℂ) :
    Matrix (((I × I) × (I × I))) (((I × I) × (I × I))) ℂ :=
  Matrix.kronecker (Matrix.kronecker (U.map star) (U.map star))
    (Matrix.kronecker U U)

/-- Normalized one-site identity and swap vectors. -/
def sitePermutation (q : ℕ) (b : Fin 2) (r : (((Fin q) × (Fin q)) × ((Fin q) × (Fin q)))) : ℂ :=
  if b=0 then
    if r.1.1=r.2.1 ∧ r.1.2=r.2.2 then (q:ℂ)⁻¹ else 0
  else if r.1.1=r.2.2 ∧ r.1.2=r.2.1 then (q:ℂ)⁻¹ else 0

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard
variable {n : Type*} [Fintype n] [DecidableEq n]

def hadamard (a b : n) (t : ℂ) : Matrix n n ℂ :=
  1 + single a a (t-1) + single b b (-t-1) + single a b t + single b a t

private theorem single_mul_rule (a b c d : n) (x y : ℂ) :
    single a b x * single c d y = if b=c then single a d (x*y) else 0 := by
  by_cases h : b=c
  · subst c; simp
  · simpa [h] using (Matrix.single_mul_single_of_ne a b c h y (l := d) (c := x))

omit [Fintype n] in
private theorem hadamard_hermitian (a b : n) (t : ℂ) (ht : star t=t) :
    (hadamard a b t).IsHermitian := by
  change (hadamard a b t)ᴴ = hadamard a b t
  simp only [hadamard,conjTranspose_add,conjTranspose_single,conjTranspose_one,
    star_sub,star_one,star_neg,ht]
  abel

private theorem hadamard_square (a b : n) (hab : a≠b) (t : ℂ) (ht : 2*t^2=1) :
    hadamard a b t * hadamard a b t = 1 := by
  have ht2 : t^2=(1/2:ℂ) := by linear_combination ht/2
  simp only [hadamard,mul_add,add_mul,one_mul,mul_one,single_mul_rule]
  simp only [hab,Ne.symm hab,if_true,if_false,zero_add,add_zero]
  ext i j
  by_cases hia : a=i <;> by_cases hib : b=i <;>
    by_cases hja : a=j <;> by_cases hjb : b=j
  all_goals subst_vars
  all_goals simp_all [Matrix.single_apply]
  all_goals ring_nf <;> norm_num [ht2]

theorem hadamard_unitary (a b : n) (hab : a≠b) (t : ℂ)
    (hreal : star t=t) (ht : 2*t^2=1) : hadamard a b t ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff,star_eq_conjTranspose,(hadamard_hermitian a b t hreal).eq]
  exact hadamard_square a b hab t ht

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Hadamard

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant
variable {n : Type*} [Fintype n] [DecidableEq n]

private def tensorCommutes (X : Matrix ((n × n)) ((n × n)) ℂ) : Prop :=
  ∀ U : Matrix.unitaryGroup n ℂ,
    X * (U.val ⊗ₖ U.val) = (U.val ⊗ₖ U.val) * X

private def quarterPhase (s : n) : Matrix n n ℂ :=
  diagonal (fun i => if i=s then Complex.I else 1)

private theorem quarterPhase_unitary (s : n) : quarterPhase s ∈ Matrix.unitaryGroup n ℂ := by
  constructor <;>
    simp only [quarterPhase,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
  all_goals
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i=s <;> simp [Matrix.diagonal,Matrix.one_apply,hi]
    · simp [Matrix.diagonal,Matrix.one_apply,hij]

private def quarterUnitary (s : n) : Matrix.unitaryGroup n ℂ := ⟨quarterPhase s,quarterPhase_unitary s⟩

private def phaseWeight (s : n) (p : (n × n)) : ℂ :=
  (if p.1=s then Complex.I else 1)*(if p.2=s then Complex.I else 1)

private theorem phase_entry_eq (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (s : n) (r c : (n × n)) :
    X r c * phaseWeight s c = phaseWeight s r * X r c := by
  have h := congrFun (congrFun (hX (quarterUnitary s)) r) c
  simpa [quarterUnitary,quarterPhase,phaseWeight,Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_diagonal,Matrix.diagonal_mul] using h

private def phaseCount (s : n) (p : (n × n)) : ℕ :=
  (if p.1=s then 1 else 0)+(if p.2=s then 1 else 0)

omit [Fintype n] in
private theorem phase_count_eq (s : n) (r c : (n × n))
    (h : phaseWeight s r = phaseWeight s c) : phaseCount s r = phaseCount s c := by
  rcases r with ⟨a,b⟩
  rcases c with ⟨c,d⟩
  by_cases ha : a=s <;> by_cases hb : b=s <;>
    by_cases hc : c=s <;> by_cases hd : d=s <;>
    simp [phaseWeight,phaseCount,ha,hb,hc,hd,Complex.I_mul_I] at h ⊢
  all_goals norm_num [Complex.ext_iff] at h

private theorem entry_support (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a b c d : n) (hz : X (a,b) (c,d) ≠ 0) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hs (s : n) : phaseCount s (c,d) = phaseCount s (a,b) := by
    apply phase_count_eq
    apply mul_right_cancel₀ hz
    simpa [mul_comm] using phase_entry_eq X hX s (a,b) (c,d)
  have ha := hs a
  have hb := hs b
  clear hs hX hz X
  by_cases hca : c=a
  · subst c
    by_cases hdb : d=b
    · subst d; exact Or.inl ⟨rfl,rfl⟩
    · have hda := ha
      by_cases hab : a=b
      · subst b
        simp [phaseCount,hdb] at ha
      · simp [phaseCount,Ne.symm hab,hdb] at hb
  · by_cases hda : d=a
    · subst d
      by_cases hcb : c=b
      · subst c; exact Or.inr ⟨rfl,rfl⟩
      · by_cases hab : a=b
        · subst b; simp [phaseCount,hca] at ha
        · simp [phaseCount,hcb,Ne.symm hab] at hb
    · simp [phaseCount,hca,hda] at ha
      omega

omit [Fintype n] in
private theorem tensor_permutation (e : Equiv.Perm n) :
    e.permMatrix ℂ ⊗ₖ e.permMatrix ℂ = Equiv.Perm.permMatrix ℂ (e.prodCongr e) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Matrix.kroneckerMap_apply,Equiv.prodCongr_apply,ite_mul,mul_ite]
  aesop

private theorem entry_permutation (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (e : Equiv.Perm n) (r c : (n × n)) :
    X ((e.prodCongr e) r) ((e.prodCongr e) c) = X r c := by
  have h := hX (D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.permutationUnitary e)
  simp only [D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.permutationUnitary,tensor_permutation,Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv,PEquiv.toMatrix_toPEquiv_mul] at h
  have hc := congrFun (congrFun h r) ((e.prodCongr e) c)
  rcases r with ⟨r1,r2⟩
  rcases c with ⟨c1,c2⟩
  simpa [Matrix.submatrix_apply] using hc.symm

omit [Fintype n] in
private theorem pair_permutation (a b c d : n) (hab : a≠b) (hcd : c≠d) :
    ∃ e : Equiv.Perm n, e a=c ∧ e b=d := by
  let f := Equiv.swap a c
  have hfc : f b≠c := by
    intro h
    have hf : f b=f a := h.trans (Equiv.swap_apply_left a c).symm
    exact hab (f.injective hf).symm
  refine ⟨f.trans (Equiv.swap (f b) d),?_,?_⟩
  · simp only [Equiv.trans_apply]
    rw [show f a=c from Equiv.swap_apply_left a c]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hfc) hcd
  · simp [Equiv.trans_apply]

private theorem uniform_diagonal (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a₀ b₀ : n) (h₀ : a₀≠b₀) (a b : n) :
    X (a,b) (a,b) = if a=b then X (a₀,a₀) (a₀,a₀) else X (a₀,b₀) (a₀,b₀) := by
  by_cases hab : a=b
  · subst b
    have h := entry_permutation X hX (Equiv.swap a₀ a) (a₀,a₀) (a₀,a₀)
    simpa using h
  · obtain ⟨e,he1,he2⟩ := pair_permutation a₀ b₀ a b h₀ hab
    have h := entry_permutation X hX e (a₀,b₀) (a₀,b₀)
    simpa [he1,he2,hab] using h

private theorem uniform_swap (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a₀ b₀ : n) (h₀ : a₀≠b₀) (a b : n) (hab : a≠b) :
    X (a,b) (b,a) = X (a₀,b₀) (b₀,a₀) := by
  obtain ⟨e,he1,he2⟩ := pair_permutation a₀ b₀ a b h₀ hab
  have h := entry_permutation X hX e (a₀,b₀) (b₀,a₀)
  simpa [he1,he2] using h

private theorem entry_zero_of_no_support (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a b c d : n)
    (h : ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c))) : X (a,b) (c,d) = 0 := by
  by_contra hz
  exact h (entry_support X hX a b c d hz)

private theorem diagonal_row (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a : n) (p : (n × n)) :
    X (a,a) p = if p=(a,a) then X (a,a) (a,a) else 0 := by
  by_cases hp : p=(a,a)
  · simp [hp]
  · simp only [hp,if_false]
    rcases p with ⟨c,d⟩
    apply entry_zero_of_no_support X hX
    simp only [Prod.mk.injEq] at hp
    aesop

private theorem offdiagonal_column (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a b : n) (hab : a≠b) (p : (n × n)) :
    X p (a,b) = if p=(a,b) then X (a,b) (a,b)
      else if p=(b,a) then X (a,b) (b,a) else 0 := by
  by_cases hp1 : p=(a,b)
  · simp [hp1]
  · simp only [hp1,if_false]
    by_cases hp2 : p=(b,a)
    · subst p
      simp only [if_true]
      exact uniform_swap X hX a b hab b a (Ne.symm hab)
    · simp only [hp2,if_false]
      rcases p with ⟨c,d⟩
      apply entry_zero_of_no_support X hX
      simp only [Prod.mk.injEq] at hp1 hp2
      exact not_or_intro hp1 hp2

private theorem hadamard_constraint (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a b : n) (hab : a≠b) :
    X (a,a) (a,a) = X (a,b) (a,b)+X (a,b) (b,a) := by
  have hroot : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  let H := Hadamard.hadamard a b ((Real.sqrt 2 / 2 : ℝ) : ℂ)
  have hHU : H ∈ Matrix.unitaryGroup n ℂ := by
    apply Hadamard.hadamard_unitary a b hab ((Real.sqrt 2 / 2 : ℝ) : ℂ) (by simp)
    push_cast
    linear_combination hroot / 2
  have hneq : (a,b)≠(b,a) := by simp [Prod.mk.injEq,hab]
  have hc := congrFun (congrFun (hX ⟨H,hHU⟩) (a,a)) (a,b)
  simp only [Matrix.mul_apply] at hc
  have hrow : (∑ k : (n × n), X (a,a) k * (H ⊗ₖ H) k (a,b)) =
      ∑ k : (n × n), (if k=(a,a) then X (a,a) (a,a) else 0) * (H ⊗ₖ H) k (a,b) :=
    Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℂ => z*(H ⊗ₖ H) k (a,b))
      (diagonal_row X hX a k))
  have hcol : (∑ k : (n × n), (H ⊗ₖ H) (a,a) k * X k (a,b)) =
      ∑ k : (n × n), (H ⊗ₖ H) (a,a) k *
        ((if k=(a,b) then X (a,b) (a,b) else 0)+(if k=(b,a) then X (a,b) (b,a) else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    rw [offdiagonal_column X hX a b hab]
    by_cases hka : k=(a,b)
    · subst k; simp [hneq]
    · by_cases hkb : k=(b,a) <;> simp [hka,hkb,hab,Ne.symm hab]
  change (∑ k : (n × n), X (a,a) k * (H ⊗ₖ H) k (a,b)) =
      ∑ k : (n × n), (H ⊗ₖ H) (a,a) k * X k (a,b) at hc
  rw [hrow,hcol] at hc
  simp only [mul_add,ite_mul,zero_mul,mul_ite,mul_zero] at hc
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hc
  simp [hneq,H,Hadamard.hadamard,Matrix.kroneckerMap_apply,hab,Ne.symm hab] at hc
  ring_nf at hc
  rw [hroot] at hc
  linear_combination 2*hc

omit [Fintype n] in
theorem replicaSwap_apply (r c : (n × n)) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) r c = if r.swap=c then 1 else 0 := by
  rcases r with ⟨a,b⟩
  rcases c with ⟨c,d⟩
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply]

private theorem two_copy_commutant (X : Matrix ((n × n)) ((n × n)) ℂ)
    (hX : tensorCommutes X) (a₀ b₀ : n) (h₀ : a₀≠b₀) :
    ∃ x y : ℂ, X=x • (1 : Matrix ((n × n)) ((n × n)) ℂ)+y • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
  refine ⟨X (a₀,b₀) (a₀,b₀),X (a₀,b₀) (b₀,a₀),?_⟩
  have hz := hadamard_constraint X hX a₀ b₀ h₀
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    replicaSwap_apply,Prod.swap_prod_mk,Prod.mk.injEq]
  by_cases hd : a=c ∧ b=d
  · rcases hd with ⟨hca,hdb⟩
    subst c d
    rw [uniform_diagonal X hX a₀ b₀ h₀ a b]
    by_cases hab : a=b
    · subst b; simp [hz]
    · simp [hab,Ne.symm hab]
  · by_cases hs : a=d ∧ b=c
    · rcases hs with ⟨had,hbc⟩
      subst d c
      have hab : a≠b := by intro h; exact hd ⟨h,h.symm⟩
      rw [uniform_swap X hX a₀ b₀ h₀ a b hab]
      simp [hd,hab,Ne.symm hab]
    · rw [entry_zero_of_no_support X hX a b c d (not_or_intro hd hs)]
      have hs' : ¬ (b=c ∧ a=d) := by simpa [and_comm] using hs
      simp [hd,hs']

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
variable {n : Type*} [Fintype n] [DecidableEq n]

def haarAverage (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix (((n × n) × (n × n))) (((n × n) × (n × n))) ℂ :=
  fun r c => ∫ U : Matrix.unitaryGroup n ℂ,
    literalMoment U.val r c ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ)))

omit [DecidableEq n] in
private theorem literalMoment_mul (A B : Matrix n n ℂ) :
    literalMoment (A*B) = literalMoment A * literalMoment B := by
  have hs : (A*B).map star = A.map star * B.map star := by
    simpa using (Matrix.map_mul (f := starRingEnd ℂ) (L := A) (M := B))
  simp only [literalMoment, Matrix.kronecker, hs]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

private theorem literalMoment_continuous (r c : ((n × n) × (n × n))) :
    Continuous (fun U : Matrix.unitaryGroup n ℂ => literalMoment U.val r c) := by
  simp only [literalMoment, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply]
  have he (i j : n) : Continuous (fun U : Matrix.unitaryGroup n ℂ => U.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact ((he _ _).star.mul (he _ _).star).mul ((he _ _).mul (he _ _))

theorem literalMoment_integrable (r c : ((n × n) × (n × n))) :
    Integrable (fun U : Matrix.unitaryGroup n ℂ => literalMoment U.val r c) ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ)))) :=
  (literalMoment_continuous r c).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem haarAverage_left_fixed (V : Matrix.unitaryGroup n ℂ) :
    literalMoment V.val * haarAverage n = haarAverage n := by
  ext i j
  simp only [Matrix.mul_apply, haarAverage]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · simp_rw [← Matrix.mul_apply, ← literalMoment_mul, ← Matrix.UnitaryGroup.mul_val]
    exact integral_mul_left_eq_self (μ := (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))))
      (fun U : Matrix.unitaryGroup n ℂ => literalMoment U.val i j) V
  · intro k hk
    exact (literalMoment_integrable k j).const_mul _

omit [Fintype n] [DecidableEq n] in
private theorem literalMoment_conjTranspose (A : Matrix n n ℂ) :
    literalMoment Aᴴ = (literalMoment A)ᴴ := by
  ext r c
  simp [literalMoment,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply,star_mul,mul_comm,mul_left_comm,mul_assoc]

private instance haar_rightInvariant : Measure.IsMulRightInvariant (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))) := by
  constructor
  intro g
  have : IsProbabilityMeasure ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))).map (fun x => x * g)) :=
    inferInstance
  have : ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))).map (fun x => x * g)).IsHaarMeasure := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ Set.univ isCompact_univ
    · simp
    · simp
    · simp
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

private instance haar_invInvariant : Measure.IsInvInvariant (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))) := by
  constructor
  have : IsProbabilityMeasure ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))).inv) := by
    unfold Measure.inv
    infer_instance
  have : ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))).inv).IsHaarMeasure := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ Set.univ isCompact_univ
    · simp
    · simp
    · simp
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

private theorem literalMoment_inv (U : Matrix.unitaryGroup n ℂ) :
    literalMoment (U⁻¹).val = (literalMoment U.val)ᴴ := by
  simpa only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using
    literalMoment_conjTranspose U.val

theorem haarAverage_hermitian : (haarAverage n).IsHermitian := by
  ext i j
  change star (∫ U : Matrix.unitaryGroup n ℂ, literalMoment U.val j i ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ)))) = _
  calc
    _ = ∫ U : Matrix.unitaryGroup n ℂ, star (literalMoment U.val j i) ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))) :=
      integral_conj.symm
    _ = ∫ U : Matrix.unitaryGroup n ℂ, literalMoment (U⁻¹).val i j ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))) := by
      congr 1
      ext U
      exact (congrFun (congrFun (literalMoment_inv U) i) j).symm
    _ = haarAverage n i j := integral_inv_eq_self
      (fun U : Matrix.unitaryGroup n ℂ => literalMoment U.val i j) ((Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ))))

theorem haarAverage_idempotent : haarAverage n * haarAverage n = haarAverage n := by
  ext i j
  change (∑ k, (∫ U : Matrix.unitaryGroup n ℂ, literalMoment U.val i k ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ)))) *
    haarAverage n k j) = haarAverage n i j
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum]
  · simp only [← Matrix.mul_apply, haarAverage_left_fixed, integral_const,
      probReal_univ, one_smul]
  · intro k hk
    exact (literalMoment_integrable i k).mul_const _

private theorem haarAverage_fixes_invariant (v : ((n × n) × (n × n)) → ℂ)
    (hv : ∀ U : Matrix.unitaryGroup n ℂ, (literalMoment U.val).mulVec v = v) :
    (haarAverage n).mulVec v = v := by
  ext i
  simp only [Matrix.mulVec,dotProduct,haarAverage]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum]
  · change (∫ U : Matrix.unitaryGroup n ℂ, ((literalMoment U.val).mulVec v) i ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup n ℂ)))) = v i
    simp only [hv,integral_const,probReal_univ,one_smul]
  · intro k hk
    exact (literalMoment_integrable i k).mul_const _

private theorem haarAverage_range_invariant (v : ((n × n) × (n × n)) → ℂ) (U : Matrix.unitaryGroup n ℂ) :
    (literalMoment U.val).mulVec ((haarAverage n).mulVec v) = (haarAverage n).mulVec v := by
  rw [Matrix.mulVec_mulVec,haarAverage_left_fixed]

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private theorem vec_unvectorize (v : ((n × n) × (n × n)) → ℂ) : Matrix.vec (Matrix.of (Function.curry (v ∘ Prod.swap))) = v := by
  ext ⟨i,j⟩
  rfl

omit [DecidableEq n] in
theorem literalMoment_vectorize (U : Matrix n n ℂ) (X : Matrix (n×n) (n×n) ℂ) :
    (literalMoment U).mulVec (Matrix.vec X) = Matrix.vec ((U ⊗ₖ U)*X*(U ⊗ₖ U)ᴴ) := by
  have hbar : U.map star ⊗ₖ U.map star = (U ⊗ₖ U).map star := by
    ext r c
    simp [Matrix.kroneckerMap_apply, star_mul, mul_comm]
  simp only [literalMoment, Matrix.kronecker]
  rw [hbar, Matrix.kronecker_mulVec_vec]
  rfl

private theorem invariant_unvectorize_commutes (v : ((n × n) × (n × n)) → ℂ)
    (hv : ∀ U : Matrix.unitaryGroup n ℂ, (literalMoment U.val).mulVec v = v) :
    Commutant.tensorCommutes (Matrix.of (Function.curry (v ∘ Prod.swap))) := by
  intro U
  have hvec := hv U
  rw [← vec_unvectorize v,literalMoment_vectorize] at hvec
  have hinj := Matrix.vec_bijective (m := n × n) (n := n × n) (R := ℂ) |>.injective
  have hc := hinj hvec
  have hU := Matrix.kronecker_mem_unitary U.property U.property
  have hs : (U.val ⊗ₖ U.val)ᴴ*(U.val ⊗ₖ U.val)=1 := hU.1
  have h := congrArg (fun X : Matrix (n×n) (n×n) ℂ => X*(U.val ⊗ₖ U.val)) hc
  simpa [mul_assoc,hs] using h.symm

theorem replicaSwap_commutes (U : Matrix n n ℂ) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * (U ⊗ₖ U) =
      (U ⊗ₖ U)*(Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
  simp only [Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [Matrix.kroneckerMap_apply,mul_comm]

theorem haarAverage_identity_fixed : (haarAverage n).mulVec ((Matrix.vec (1 : Matrix (n×n) (n×n) ℂ))) = (Matrix.vec (1 : Matrix (n×n) (n×n) ℂ)) := by
  apply haarAverage_fixes_invariant
  intro U
  rw [literalMoment_vectorize]
  congr 1
  rw [mul_one]
  exact (Matrix.kronecker_mem_unitary U.property U.property).2

theorem haarAverage_swap_fixed : (haarAverage n).mulVec ((Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)))) = (Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))) := by
  apply haarAverage_fixes_invariant
  intro U
  rw [literalMoment_vectorize]
  congr 1
  rw [← replicaSwap_commutes,mul_assoc]
  have hU := (Matrix.kronecker_mem_unitary U.property U.property).2
  simp only [Matrix.star_eq_conjTranspose] at hU
  rw [hU,mul_one]

theorem haarAverage_image_span (v : ((n × n) × (n × n)) → ℂ) (a b : n) (hab : a≠b) :
    ∃ x y : ℂ, (haarAverage n).mulVec v = x • (Matrix.vec (1 : Matrix (n×n) (n×n) ℂ))+y • (Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))) := by
  have hcomm := invariant_unvectorize_commutes ((haarAverage n).mulVec v)
    (haarAverage_range_invariant v)
  obtain ⟨x,y,hxy⟩ := Commutant.two_copy_commutant _ hcomm a b hab
  refine ⟨x,y,?_⟩
  have h := congrArg Matrix.vec hxy
  rw [vec_unvectorize] at h
  exact h

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

namespace D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

def localPermutation (q : ℕ) (b : Fin 2 × Fin 2) (r : (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q)))) : ℂ :=
  sitePermutation q b.1 ((r.1.1.1,r.1.2.1),(r.2.1.1,r.2.2.1)) *
    sitePermutation q b.2 ((r.1.1.2,r.1.2.2),(r.2.1.2,r.2.2.2))

private theorem sitePermutation_real (q : ℕ) (b : Fin 2) :
    star (sitePermutation q b) = sitePermutation q b := by
  ext r
  simp only [Pi.star_apply, sitePermutation]
  split_ifs <;> simp

private theorem sitePermutation_gram (q : ℕ) (hq : 0<q) (b c : Fin 2) :
    star (sitePermutation q b) ⬝ᵥ sitePermutation q c = if b=c then 1 else (q:ℂ)⁻¹ := by
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [sitePermutation_real]
  fin_cases b <;> fin_cases c <;>
    simp [sitePermutation,dotProduct,Fintype.sum_prod_type,ite_and,ite_mul,mul_ite,
      Finset.sum_ite_eq',hq0,eq_comm]
  all_goals field_simp
  all_goals ring

theorem localPermutation_gram (q : ℕ) (hq : 0<q) (b c : Fin 2 × Fin 2) :
    star (localPermutation q b) ⬝ᵥ localPermutation q c =
      (if b.1=c.1 then 1 else (q:ℂ)⁻¹)*(if b.2=c.2 then 1 else (q:ℂ)⁻¹) := by
  simp only [dotProduct,localPermutation,Pi.star_apply,star_mul]
  have hsum := (((Equiv.prodProdProdComm (Fin q) (Fin q) (Fin q) (Fin q)).prodCongr (Equiv.prodProdProdComm (Fin q) (Fin q) (Fin q) (Fin q))).trans
    (Equiv.prodProdProdComm (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q))).sum_comp
    (fun r : (((Fin q) × (Fin q)) × ((Fin q) × (Fin q))) × (((Fin q) × (Fin q)) × ((Fin q) × (Fin q))) =>
      (star (sitePermutation q b.2 r.2)*star (sitePermutation q b.1 r.1))*
        (sitePermutation q c.1 r.1*sitePermutation q c.2 r.2))
  simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,Equiv.prodProdProdComm_apply] at hsum
  rw [hsum,Fintype.sum_prod_type]
  calc
    _ = (star (sitePermutation q b.1) ⬝ᵥ sitePermutation q c.1)*
      (star (sitePermutation q b.2) ⬝ᵥ sitePermutation q c.2) := by
      simp only [dotProduct,Pi.star_apply,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [sitePermutation_gram q hq,sitePermutation_gram q hq]

private theorem local_identity (q : ℕ) :
    localPermutation q (0,0) = ((q:ℂ)^2)⁻¹ • (Matrix.vec (1 : Matrix ((Fin q × Fin q) × (Fin q × Fin q)) ((Fin q × Fin q) × (Fin q × Fin q)) ℂ)) := by
  ext ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  simp only [localPermutation,Equiv.prodProdProdComm,Equiv.prodCongr,Equiv.trans,Equiv.coe_fn_mk,sitePermutation,
    Matrix.vec,Matrix.one_apply,Prod.mk.injEq,Pi.smul_apply,smul_eq_mul]
  by_cases h1 : a=e <;> by_cases h2 : c=g <;> by_cases h3 : b=f <;>
    by_cases h4 : d=h <;> simp [h1,h2,h3,h4,pow_two,_root_.mul_inv_rev,eq_comm]

private theorem local_swap (q : ℕ) :
    localPermutation q (1,1) = ((q:ℂ)^2)⁻¹ • (Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin q × Fin q) (Fin q × Fin q)))) := by
  ext ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  simp only [localPermutation,Equiv.prodProdProdComm,Equiv.prodCongr,Equiv.trans,Equiv.coe_fn_mk,sitePermutation,
    Matrix.vec,Commutant.replicaSwap_apply,Prod.swap_prod_mk,
    Prod.mk.injEq,Pi.smul_apply,smul_eq_mul]
  by_cases h1 : a=g <;> by_cases h2 : c=e <;> by_cases h3 : b=h <;>
    by_cases h4 : d=f <;> simp [h1,h2,h3,h4,pow_two,_root_.mul_inv_rev,eq_comm]

theorem local_identity_fixed (q : ℕ) :
    (haarAverage (Fin q × Fin q)).mulVec (localPermutation q (0,0)) = localPermutation q (0,0) := by
  change (haarAverage ((Fin q × Fin q))).mulVec _ = _
  rw [local_identity,Matrix.mulVec_smul,haarAverage_identity_fixed]

theorem local_swap_fixed (q : ℕ) :
    (haarAverage (Fin q × Fin q)).mulVec (localPermutation q (1,1)) = localPermutation q (1,1) := by
  change (haarAverage ((Fin q × Fin q))).mulVec _ = _
  rw [local_swap,Matrix.mulVec_smul,haarAverage_swap_fixed]

theorem hermitian_fixed_pairing {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) (hP : P.IsHermitian) (u v : n → ℂ)
    (hu : P.mulVec u = u) : star u ⬝ᵥ P.mulVec v = star u ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← hP.eq, vecMul_conjTranspose, star_star, hu]

private theorem gate_image_local_span (q : ℕ) (hq : 2≤q) (v : (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) → ℂ) :
    ∃ x y : ℂ, (haarAverage (Fin q × Fin q)).mulVec v =
      x • localPermutation q (0,0)+y • localPermutation q (1,1) := by
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast (show q≠0 by omega)
  let a : (Fin q × Fin q) := (⟨0,by omega⟩,⟨0,by omega⟩)
  let b : (Fin q × Fin q) := (⟨1,by omega⟩,⟨0,by omega⟩)
  have hab : a≠b := by intro h; have := congrArg (fun r => r.1.val) h; simp [a,b] at this
  obtain ⟨x,y,hxy⟩ := haarAverage_image_span v a b hab
  refine ⟨x*(q:ℂ)^2,y*(q:ℂ)^2,?_⟩
  change (haarAverage ((Fin q × Fin q))).mulVec v = _
  rw [hxy,local_identity,local_swap,smul_smul,smul_smul]
  simp [hq0,mul_assoc]

theorem gate_mixed_rule (q : ℕ) (hq : 2≤q) (b : Fin 2 × Fin 2) (hb : b.1≠b.2) :
    (haarAverage (Fin q × Fin q)).mulVec (localPermutation q b) =
      ((q:ℂ)/((q:ℂ)^2+1)) •
        (localPermutation q (0,0)+localPermutation q (1,1)) := by
  obtain ⟨x,y,hxy⟩ := gate_image_local_span q hq (localPermutation q b)
  have hp := hermitian_fixed_pairing (haarAverage (Fin q × Fin q))
    (haarAverage_hermitian (n := (Fin q × Fin q)))
  have h0 := hp (localPermutation q (0,0)) (localPermutation q b) (local_identity_fixed q)
  have h1 := hp (localPermutation q (1,1)) (localPermutation q b) (local_swap_fixed q)
  rw [hxy,dotProduct_add,dotProduct_smul,dotProduct_smul] at h0 h1
  simp only [smul_eq_mul] at h0 h1
  simp only [localPermutation_gram q (by omega)] at h0 h1
  have he : (if (0:Fin 2)=b.1 then 1 else (q:ℂ)⁻¹)*
      (if (0:Fin 2)=b.2 then 1 else (q:ℂ)⁻¹) = (q:ℂ)⁻¹ := by
    rcases b with ⟨b,c⟩
    fin_cases b <;> fin_cases c <;> simp_all
  have he' : (if (1:Fin 2)=b.1 then 1 else (q:ℂ)⁻¹)*
      (if (1:Fin 2)=b.2 then 1 else (q:ℂ)⁻¹) = (q:ℂ)⁻¹ := by
    rcases b with ⟨b,c⟩
    fin_cases b <;> fin_cases c <;> simp_all
  simp only [Fin.isValue,ite_true,ite_false,
    show ¬(0:Fin 2)=1 by decide,show ¬(1:Fin 2)=0 by decide,one_mul,he,he'] at h0 h1
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast (show q≠0 by omega)
  have hden : (q:ℂ)^2+1 ≠ 0 := by
    exact_mod_cast (show q^2+1≠0 by omega)
  have hs : (q:ℂ)^2-1 ≠ 0 := by
    have hr : (2:ℝ)≤(q:ℝ) := by exact_mod_cast hq
    exact_mod_cast (show (q:ℝ)^2-1≠0 by nlinarith)
  field_simp [hq0] at h0 h1
  have hsub : ((q:ℂ)^2-1)*(x-y)=0 := by linear_combination h0-h1
  have hsame : x=y := sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hs)
  have hx : x = (q:ℂ)/((q:ℂ)^2+1) := by
    apply (eq_div_iff hden).mpr
    rw [← hsame] at h0
    linear_combination h0
  have hy : y = (q:ℂ)/((q:ℂ)^2+1) := hsame.symm.trans hx
  rw [hxy,hx,hy,smul_add]

open scoped BigOperators

theorem trace_one_sandwich {d : ℕ} (p x : Matrix (Fin d) (Fin d) ℂ)
    (hpp : p * p = p) (htr : p.trace = 1) :
    p * x * p = (p * x).trace • p := by
  let f := Matrix.toLin' p
  have hf : IsIdempotentElem f := by
    change f * f = f
    simpa only [f, Module.End.mul_eq_comp, ← Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hpp
  have hdim : Module.finrank ℂ (LinearMap.range f) = 1 := by
    have ht := ((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf).trace
    rw [Matrix.trace_toLin'_eq, htr] at ht
    exact_mod_cast ht.symm
  let t : LinearMap.range f →ₗ[ℂ] LinearMap.range f :=
    (f.rangeRestrict.comp (Matrix.toLin' x)).comp (LinearMap.range f).subtype
  obtain ⟨c, hc, hu⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim t
  have hmat : p * x * p = c • p := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun z : LinearMap.range f => (z : Fin d → ℂ))
      (LinearMap.congr_fun hc (f.rangeRestrict v))
    change f ((Matrix.toLin' x) (f v)) = c • f v at hv
    simpa only [f, Matrix.toLin'_mul_apply, map_smul, LinearMap.smul_apply] using hv
  have hcval : c = (p * x).trace := by
    have ht := congrArg Matrix.trace hmat
    rw [Matrix.trace_smul, htr, smul_eq_mul, mul_one,
      Matrix.trace_mul_cycle, hpp] at ht
    exact ht.symm
  simpa only [hcval] using hmat

section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem swapHermitian : ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))).IsHermitian := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [Matrix.conjTranspose_apply, Prod.swap_prod_mk, Prod.mk.injEq]
  simp [and_comm, eq_comm]

theorem swapSquare : (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) = 1 := by
  have h : Equiv.prodComm n n * Equiv.prodComm n n = (1 : Equiv.Perm (n×n)) := by
    ext x <;> rfl
  simp [← Matrix.permMatrix_mul, h]

theorem traceSwap : Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))) = (Fintype.card n : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp [Prod.ext_iff, eq_comm]

private theorem twirlTrace (Y : Matrix (n×n) (n×n) ℂ) :
    Matrix.trace (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = Matrix.trace Y := by
  have h := hermitian_fixed_pairing (haarAverage n) haarAverage_hermitian
    (Matrix.vec (1 : Matrix (n×n) (n×n) ℂ)) (Matrix.vec Y) haarAverage_identity_fixed
  have hv : Matrix.vec (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = (haarAverage n).mulVec (Matrix.vec Y) := by rfl
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec] at h
  simpa using h

private theorem twirlSwapTrace (Y : Matrix (n×n) (n×n) ℂ) :
    Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) := by
  have h := hermitian_fixed_pairing (haarAverage n) haarAverage_hermitian
    (Matrix.vec ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)))) (Matrix.vec Y) haarAverage_swap_fixed
  have hv : Matrix.vec (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = (haarAverage n).mulVec (Matrix.vec Y) := by rfl
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec,
      swapHermitian.eq] at h
  exact h

theorem twirlFormula (Y : Matrix (n×n) (n×n) ℂ) (hN : 2 ≤ Fintype.card n) :
    Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap)) =
      ((Matrix.trace Y - Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (1 : Matrix (n×n) (n×n) ℂ) +
      ((Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) - Matrix.trace Y / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
  letI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne n
  obtain ⟨x,y,hxy⟩ := haarAverage_image_span (Matrix.vec Y) a b hab
  have hv : Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap)) = x • (1 : Matrix (n×n) (n×n) ℂ) + y • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
    ext r c
    change ((haarAverage n).mulVec (Matrix.vec Y)) (c,r) = _
    exact congrFun hxy (c,r)
  have h0 := twirlTrace Y
  have h1 := twirlSwapTrace Y
  rw [hv, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, traceSwap] at h0
  rw [hv, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      swapSquare, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      traceSwap, Matrix.trace_one] at h1
  simp only [Fintype.card_prod, Nat.cast_mul, smul_eq_mul] at h0 h1
  have hn : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast (show Fintype.card n ≠ 0 by omega)
  have hden : (Fintype.card n : ℂ)^2 - 1 ≠ 0 := by
    have hi : (2 : ℤ) ≤ Fintype.card n := by exact_mod_cast hN
    have hz : (Fintype.card n : ℤ)^2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast hz
  have hx : x = (Matrix.trace Y - Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) / (Fintype.card n : ℂ)) /
      ((Fintype.card n : ℂ)^2 - 1) := by
    rw [← h0, ← h1]
    field_simp [hn, hden]
    <;> ring
  have hy : y = (Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) - Matrix.trace Y / (Fintype.card n : ℂ)) /
      ((Fintype.card n : ℂ)^2 - 1) := by
    rw [← h0, ← h1]
    field_simp [hn, hden]
    <;> ring
  rw [hv, hx, hy]

end

private theorem pure_twirl {d : ℕ} [NeZero d] :
    (haarAverage (Fin d)).mulVec
        (Matrix.vec (Matrix.single (0, 0) (0, 0) (1 : ℂ))) =
      (1 / ((d : ℂ) * (d + 1))) •
        (Matrix.vec (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
          Matrix.vec (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)))) := by
  classical
  by_cases hd : d = 1
  · subst d
    have hy : (Matrix.single (0, 0) (0, 0) (1 : ℂ) :
        Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = 1 := by
      simpa only [Fintype.sum_prod_type, Fin.sum_univ_one] using
        (Matrix.sum_single_one (m := Fin 1 × Fin 1) (α := ℂ))
    rw [hy, haarAverage_identity_fixed]
    ext r
    simp [Matrix.vec, Matrix.one_apply, Equiv.Perm.permMatrix, Subsingleton.elim r.1 (0, 0),
      Subsingleton.elim r.2 (0, 0)]
  have hd2 : 2 ≤ d := by have := NeZero.ne d; omega
  have h := twirlFormula (Matrix.single (0, 0) (0, 0) (1 : ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (by simpa only [Fintype.card_fin] using hd2)
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hnm1 : (d - 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (d : ℤ) - 1 ≠ 0 by omega)
  have hn1 : (d + 1 : ℂ) ≠ 0 := by exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hden : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have he : (d : ℂ) ^ 2 - 1 = (d - 1) * (d + 1) := by ring
    rw [he]
    exact mul_ne_zero hnm1 hn1
  have hc : (1 - 1 / (d : ℂ)) / ((d : ℂ) ^ 2 - 1) =
      1 / ((d : ℂ) * (d + 1)) := by
    field_simp [hn, hn1, hden]
    <;> ring
  have ht : Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))) *
      (Matrix.single (0, 0) (0, 0) (1 : ℂ))) = 1 := by
    simp [Matrix.trace_mul_single, Equiv.Perm.permMatrix]
  simp only [Matrix.trace_single_eq_same, ht, Fintype.card_fin, hc] at h
  have hv := congrArg Matrix.vec h
  rw [Matrix.vec_add, Matrix.vec_smul, Matrix.vec_smul, ← smul_add] at hv
  exact hv

private theorem pure_tensor_integral {d : ℕ} [NeZero d] :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
      (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ⊗ₖ
        (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ∂(Measure.haarMeasure
          (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      (1 / ((d : ℂ) * (d + 1))) •
        (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))) := by
  classical
  let z := fun u : Matrix.unitaryGroup (Fin d) ℂ =>
    (u.1 * Matrix.single 0 0 1 * u.1ᴴ) ⊗ₖ (u.1 * Matrix.single 0 0 1 * u.1ᴴ)
  have hp (u : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
      ((u.1 * Matrix.single 0 0 1 * u.1ᴴ) : Matrix (Fin d) (Fin d) ℂ) i j =
        u.1 i 0 * star (u.1 j 0) := by
    rw [Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    simp [Matrix.vecMulVec_apply, Matrix.single_vecMul, Matrix.conjTranspose_apply]
  have hz : Continuous z := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    convert literalMoment_continuous (c, r) ((0, 0), (0, 0)) using 1
    funext u
    simp only [z, Matrix.kroneckerMap_apply, hp, literalMoment, Matrix.kronecker, Matrix.map_apply]
    ring
  have hi := hz.integrable_of_hasCompactSupport
    (μ := Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))
    (HasCompactSupport.of_compactSpace z)
  ext r c
  have heval : (∫ u, z u ∂_) r c = ∫ u, z u r c ∂_ :=
    (congrFun (eval_integral (fun r => hi.eval r) r) c).trans
      (eval_integral (fun c => (hi.eval r).eval c) c)
  rw [heval]
  have h := congrFun (pure_twirl (d := d)) (c, r)
  simp only [Matrix.vec_single, Matrix.mulVec_single_one] at h
  change (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
    literalMoment u.1 (c, r) ((0, 0), (0, 0)) ∂_) = _ at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with u
    simp only [z, Matrix.kroneckerMap_apply, hp, literalMoment, Matrix.kronecker, Matrix.map_apply]
    ring
  · rfl

theorem pure_quadratic {d : ℕ} [NeZero d] (a : Matrix (Fin d) (Fin d) ℂ) :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
      Matrix.trace ((u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a *
        (u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a) ∂(Measure.haarMeasure
          (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      (a.trace ^ 2 + (a * a).trace) / ((d : ℂ) * (d + 1)) := by
  classical
  let q : Matrix (Fin d) (Fin d) ℂ := Matrix.single 0 0 1
  let p := fun u : Matrix.unitaryGroup (Fin d) ℂ => u.1 * q * u.1ᴴ
  let z := fun u : Matrix.unitaryGroup (Fin d) ℂ => p u ⊗ₖ p u
  have hp : Continuous p :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hz : Continuous z := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    exact (hp.matrix_elem r.1 c.1).mul (hp.matrix_elem r.2 c.2)
  have hi := hz.integrable_of_hasCompactSupport
    (μ := Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))
    (HasCompactSupport.of_compactSpace z)
  let f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin d × Fin d) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ (a ⊗ₖ a))).toContinuousLinearMap
  have heq : ∀ u, f (z u) = (p u * a * p u * a).trace := by
    intro u
    change ((a ⊗ₖ a) * (p u ⊗ₖ p u)).trace = _
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
    have hpp : p u * p u = p u := by
      have hb : IsIdempotentElem (Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ)) := by
        change Matrix.single (0 : Fin d) 0 (1 : ℂ) * Matrix.single 0 0 1 = Matrix.single 0 0 1
        simpa only [mul_one] using
          Matrix.single_mul_single_same (1 : ℂ) (0 : Fin d) (0 : Fin d) (0 : Fin d) 1
      change (u.1 * Matrix.single 0 0 1 * u.1ᴴ) * (u.1 * Matrix.single 0 0 1 * u.1ᴴ) =
        u.1 * Matrix.single 0 0 1 * u.1ᴴ
      simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        (hb.map (Unitary.conjStarAlgAut ℂ _ u)).eq
    have hpt : (p u).trace = 1 :=
      (Matrix.trace_units_conj (Unitary.toUnits u) q).trans (Matrix.trace_single_eq_same _ _)
    rw [trace_one_sandwich (p u) a hpp hpt,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm a (p u)]
  have hs : ((a ⊗ₖ a) *
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))).trace =
        (a * a).trace := by
    rw [PEquiv.mul_toMatrix_toPEquiv]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Function.id_def,
      Equiv.prodComm_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Matrix.mul_apply]
    rfl
  calc
    (∫ u, (p u * a * p u * a).trace ∂_) = ∫ u, f (z u) ∂_ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => (heq u).symm)
    _ = f (∫ u, z u ∂_) := f.integral_comp_comm hi
    _ = _ := by
      rw [show (∫ u, z u ∂_) = _ from pure_tensor_integral (d := d)]
      change ((a ⊗ₖ a) * ((1 / ((d : ℂ) * (d + 1))) •
        (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))))).trace = _
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_one,
        Matrix.trace_add, Matrix.trace_kronecker, hs]
      simp [pow_two, div_eq_mul_inv, mul_comm]

end D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
