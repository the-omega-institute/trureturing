/- GID: D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full alternating tensor restrictions of arbitrary squarefree support operators. -/
import D5.S3.Combinatorics.SpectralGraph.RepeatedPairSupport

/-! Source: squarefree.tex, PR3 b93becea662a746badeadba42fdc3d3eb3db9382,
blob 2cd18d52cd3f4581d624bb94006480340756a5c3. Every paired coordinate
is retained. The alternating functions vanish at the omitted empty and full
supports, and the full actual ideal-graph lift is the existing general-index
repeated-pair lift. These are operator identities, not scalar proxy premises. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.SquarefreeAlternatingSupport
open RepeatedPairSupport IdealIntersectionSupport IdealIntersectionObstructions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def E : Matrix (Finset ι) (Finset ι) ℝ :=
  diagonal (diagonalFactor (fun _ : ι => (1 : ℝ)))

def F : Matrix (Finset ι) (Finset ι) ℝ :=
  disjointKernel (fun _ : ι => (1 : ℝ))

private theorem diagonal_pair (A : Finset (Fin 2)) (T : Finset ι) :
    diagonalFactor (fun _ : Fin 2 ⊕ ι => (1 : ℝ)) (A.disjSum T) =
      (2 : ℝ) ^ (2-A.card) * diagonalFactor (fun _ : ι => (1 : ℝ)) T := by
  have hu : (univ : Finset (Fin 2 ⊕ ι)) =
      (univ : Finset (Fin 2)).disjSum (univ : Finset ι) := by
    ext i
    cases i <;> simp
  have hd : (univ : Finset (Fin 2 ⊕ ι)) \ A.disjSum T =
      ((univ : Finset (Fin 2)) \ A).disjSum ((univ : Finset ι) \ T) := by
    ext i
    cases i <;> simp
  simp [diagonalFactor,hd,Finset.card_sdiff,show (1 : ℝ)+1=2 by norm_num,pow_add]

/-- Each alternating pair contributes the determinant two of the full E factor. -/
theorem E_action (h : Finset ι → ℝ) :
    E *ᵥ pairedValue h = (2 : ℝ) • pairedValue (E *ᵥ h) := by
  ext S
  have hs : S = S.toLeft.disjSum S.toRight := by ext i; cases i <;> simp
  rw [hs]
  simp only [E,mulVec_diagonal,Pi.smul_apply,smul_eq_mul,diagonal_pair,pairedValue_sum]
  split_ifs with h0 h1
  · simp [h0]
    ring
  · simp [h1]
    ring
  · simp

/-- Each alternating pair contributes the determinant minus one of the full F factor. -/
theorem F_action (h : Finset ι → ℝ) :
    F *ᵥ pairedValue h = -pairedValue (F *ᵥ h) := by
  ext S
  have hs : S = S.toLeft.disjSum S.toRight := by ext i; cases i <;> simp
  rw [hs]
  generalize S.toLeft = A
  generalize S.toRight = T
  have hA : A ∈ ({∅,{0},{1},univ} : Finset (Finset (Fin 2))) := by
    have he : ({∅,{0},{1},univ} : Finset (Finset (Fin 2))) = univ := by decide
    rw [he]
    exact mem_univ _
  simp only [mem_insert,mem_singleton] at hA
  simp only [F,mulVec,dotProduct,sum_four,disjointKernel,disjoint_sum,
    pairedValue_sum,prod_const_one,ite_mul,zero_mul,one_mul,Pi.neg_apply]
  rcases hA with rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide) [show (univ : Finset (Fin 2)) ≠ {0} by decide,
      show (univ : Finset (Fin 2)) ≠ {1} by decide,
      show (univ : Finset (Fin 2)) ≠ ∅ by decide,
      ←sum_add_distrib,←sum_neg_distrib]
  · apply Finset.sum_eq_zero
    intro U _
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro U _
    split_ifs <;> ring

/-- All paired prime coordinates, with a freely chosen remaining coordinate type. -/
@[reducible] def Index (r : ℕ) (β : Type*) : Type _ :=
  match r with
  | 0 => β
  | r+1 => Fin 2 ⊕ Index r β

instance indexFintype (r : ℕ) (β : Type*) [Fintype β] : Fintype (Index r β) :=
  match r with
  | 0 => inferInstanceAs (Fintype β)
  | r+1 =>
    letI := indexFintype r β
    inferInstanceAs (Fintype (Fin 2 ⊕ Index r β))

instance indexDecidableEq (r : ℕ) (β : Type*) [DecidableEq β] : DecidableEq (Index r β) :=
  match r with
  | 0 => inferInstanceAs (DecidableEq β)
  | r+1 =>
    letI := indexDecidableEq r β
    inferInstanceAs (DecidableEq (Fin 2 ⊕ Index r β))

variable {β : Type*} [Fintype β] [DecidableEq β]

def lift (r : ℕ) (h : Finset β → ℝ) : Finset (Index r β) → ℝ :=
  match r with
  | 0 => h
  | r+1 => pairedValue (lift r h)

private theorem paired_smul (t : ℝ) (h : Finset ι → ℝ) :
    pairedValue (t • h) = t • pairedValue h := by
  ext S
  simp only [pairedValue,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

private theorem paired_add (f g : Finset ι → ℝ) :
    pairedValue (f+g) = pairedValue f+pairedValue g := by
  ext S
  simp only [pairedValue,Pi.add_apply]
  split_ifs <;> ring

theorem lift_smul (r : ℕ) (t : ℝ) (h : Finset β → ℝ) :
    lift r (t • h) = t • lift r h := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [lift,ih] using paired_smul t (lift r h)

theorem lift_add (r : ℕ) (f g : Finset β → ℝ) :
    lift r (f+g) = lift r f+lift r g := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [lift,ih] using paired_add (lift r f) (lift r g)

/-- No nonzero remaining vector is lost by any number of alternating pairs. -/
theorem lift_nonzero (r : ℕ) (h : Finset β → ℝ) (hh : h ≠ 0) : lift r h ≠ 0 := by
  induction r with
  | zero => exact hh
  | succ r ih =>
    obtain ⟨T,hT⟩ := Function.ne_iff.mp ih
    apply Function.ne_iff.mpr
    refine ⟨({0} : Finset (Fin 2)).disjSum T,?_⟩
    simpa only [lift,pairedValue_sum,ite_true,Pi.zero_apply] using hT

/-- Full E intertwining for every alternating tensor, not merely its energy. -/
theorem E_lift (r : ℕ) (h : Finset β → ℝ) :
    E *ᵥ lift r h = (2 : ℝ)^r • lift r (E *ᵥ h) := by
  induction r with
  | zero => simp only [lift,pow_zero,one_smul]
  | succ r ih =>
    rw [lift,E_action,ih,paired_smul]
    simp only [lift,pow_succ,smul_smul]
    congr 1
    ring

/-- Full F intertwining, including every zero cell outside the alternating support. -/
theorem F_lift (r : ℕ) (h : Finset β → ℝ) :
    F *ᵥ lift r h = (-1 : ℝ)^r • lift r (F *ᵥ h) := by
  induction r with
  | zero => simp only [lift,pow_zero,one_smul]
  | succ r ih =>
    rw [lift,F_action,ih,paired_smul]
    simp only [lift,pow_succ,neg_smul]
    ext S
    simp only [Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
    ring

/-- The entire repeated-pair operator reduces on every alternating tensor
to the exact two summands in the original squarefree argument. -/
theorem K_lift (r : ℕ) (h : Finset β → ℝ) :
    K 1 (fun _ : Index r β => (1 : ℝ)) *ᵥ lift r h =
      (2 : ℝ)^(r+1) • lift r (E *ᵥ h) +
        (-1 : ℝ)^r • lift r (F *ᵥ h) := by
  have hK : K (1 : ℝ) (fun _ : Index r β => (1 : ℝ)) = (2 : ℝ) • E + F := by
    ext S T
    simp [K,E,F,Matrix.diagonal,Matrix.smul_apply]
    split_ifs <;> ring
  rw [hK,add_mulVec,smul_mulVec]
  rw [E_lift,F_lift,smul_smul]
  congr 2
  rw [pow_succ]
  ring

/-- The full residual operator after all pairs, on all remaining subsets. -/
def reduced (r : ℕ) : Matrix (Finset β) (Finset β) ℝ :=
  (2 : ℝ)^(r+1) • E + (-1 : ℝ)^r • F

/-- Exact invariant-subspace intertwining of the two full operators. -/
theorem reduced_intertwining (r : ℕ) (h : Finset β → ℝ) :
    K 1 (fun _ : Index r β => (1 : ℝ)) *ᵥ lift r h =
      lift r (reduced r *ᵥ h) := by
  rw [K_lift,reduced,add_mulVec,smul_mulVec,smul_mulVec,lift_add,lift_smul,lift_smul]

set_option maxHeartbeats 2000000 in
/-- Every residual eigenpair gives an actual squarefree ideal-graph eigenvalue,
with arbitrary distinct prime values and all original paired coordinates. -/
theorem actual_eigenvalue (r : ℕ) (p : Fin 2 ⊕ Index r β → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (e : ℝ) (h : Finset β → ℝ) (hh : h ≠ 0)
    (he : reduced r *ᵥ h = e • h) :
    HasActualEigenvalue
      (modulus p (pairExponents 1 (fun _ : Index r β => 1)))
      (((4*(∏ _ : Index r β, (2 : ℕ))-2 : ℕ) : ℝ)+1-e) := by
  have hfull : K (1 : ℝ) (fun _ : Index r β => (1 : ℝ)) *ᵥ lift r h =
      e • lift r h := by
    rw [reduced_intertwining,he,lift_smul]
  simpa using RepeatedPairSupport.actual_paired_eigenvalue p hp hinj 1
    (fun _ : Index r β => 1) (by decide) (fun _ => by decide) e (lift r h)
    (lift_nonzero r h hh) (by simpa only [Nat.cast_one] using hfull)

end D5.S3.Combinatorics.SpectralGraph.SquarefreeAlternatingSupport
