/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_certificate
   digest: Actual two-row and three-row column continuations with the isolated class. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

/-! Columns are read from the independently defined diagonal strip graph. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
open HardinThinGraphTransport (stripGraph)

abbrev Column (h : ℕ) := Fin (h+1) → Fin 3
/-- All horizontal and diagonal bonds between the actual adjacent columns. -/
def cross {h : ℕ} (p q : Column h) : Prop :=
  (∀ i, p i ≠ q i) ∧ ∀ i : Fin h,
    p i.castSucc ≠ q i.succ ∧ p i.succ ≠ q i.castSucc
instance {h : ℕ} (p q : Column h) : Decidable (cross p q) :=
  inferInstanceAs (Decidable ((∀ _, _) ∧ ∀ _, _ ∧ _))

private def tailGood {h : ℕ} : {k : ℕ} → Column h → (Fin k → Column h) → Prop
  | 0, _, _ => True
  | _+1, p, f => cross p (f 0) ∧ tailGood (f 0) (Fin.tail f)
private instance {h k : ℕ} (p : Column h) (f : Fin k → Column h) : Decidable (tailGood p f) := by
  induction k generalizing p with
  | zero => exact isTrue trivial
  | succ k ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)

def columnV {h : ℕ} : ℕ → Column h → ℕ
  | 0, _ => 1
  | k+1, p => ∑ q : Column h, if cross p q then columnV k q else 0

private theorem tail_local {h : ℕ} (k : ℕ) (f : Fin (k+1) → Column h) :
    tailGood (f 0) (Fin.tail f) ↔ ∀ j : Fin k, cross (f j.castSucc) (f j.succ) := by
  induction k with
  | zero => simp [tailGood]
  | succ k ih =>
    have ht := ih (Fin.tail f)
    simp only [Fin.forall_fin_succ, tailGood, Fin.tail] at ht ⊢
    tauto

private theorem coloring_local (h k : ℕ) (f : Fin (k+1) → Column h) :
    (∀ a b, (stripGraph true h k).Adj a b → f a.2 a.1 ≠ f b.2 b.1) ↔
      ∀ j : Fin k, cross (f j.castSucc) (f j.succ) := by
  constructor
  · intro hc j
    exact ⟨fun i => hc _ _ (Or.inl (Or.inl ⟨i,j,rfl,rfl⟩)),
      fun i => ⟨hc _ _ (Or.inl (Or.inr ⟨i,j,Or.inl ⟨rfl,rfl⟩⟩)),
        hc _ _ (Or.inr (Or.inr ⟨i,j,Or.inr ⟨rfl,rfl⟩⟩))⟩⟩
  · intro hc
    have forward : ∀ a b : Fin (h+1) × Fin (k+1),
        (∃ i : Fin (h+1), ∃ j : Fin k, a = (i,j.castSucc) ∧ b = (i,j.succ)) ∨
        (∃ i : Fin h, ∃ j : Fin k,
          (a = (i.castSucc,j.castSucc) ∧ b = (i.succ,j.succ)) ∨
          (a = (i.castSucc,j.succ) ∧ b = (i.succ,j.castSucc))) →
        f a.2 a.1 ≠ f b.2 b.1 := by
      intro a b hab
      rcases hab with ⟨i,j,rfl,rfl⟩ | ⟨i,j,hab | hab⟩
      · exact (hc j).1 i
      · rcases hab with ⟨rfl,rfl⟩; exact ((hc j).2 i).1
      · rcases hab with ⟨rfl,rfl⟩; exact ((hc j).2 i).2.symm
    intro a b hab
    exact hab.elim (forward a b) (fun hh => (forward b a hh).symm)

/-- Reading columns and reconstructing all cells are inverse maps. -/
noncomputable def coloringEquiv (h k : ℕ) :
    (stripGraph true h k).Coloring (Fin 3) ≃
      {f : Fin (k+1) → Column h // tailGood (f 0) (Fin.tail f)} where
  toFun p := ⟨fun j i => p (i,j), (tail_local k (fun j i => p (i,j))).mpr
    ((coloring_local h k (fun j i => p (i,j))).mp (fun a b hh => p.valid hh))⟩
  invFun f := SimpleGraph.Coloring.mk (fun a => f.val a.2 a.1)
    (by intro a b hh; exact (coloring_local h k f.val).mpr ((tail_local k _).mp f.property) a b hh)
  left_inv p := DFunLike.ext _ _ (fun _ => rfl)
  right_inv f := Subtype.ext rfl

private theorem tail_count {h : ℕ} (k : ℕ) (p : Column h) :
    (∑ f : Fin k → Column h, if tailGood p f then 1 else 0) = columnV k p := by
  induction k generalizing p with
  | zero => simp [tailGood, columnV]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Column h)).sum_comp, Fintype.sum_prod_type]
    change (∑ q : Column h, ∑ f : Fin k → Column h,
      if tailGood p (Fin.cons q f) then 1 else 0) = _
    rw [columnV]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hc : cross p q <;> simp [tailGood,hc,ih]

private theorem graph_count (h k : ℕ) :
    Nat.card ((stripGraph true h k).Coloring (Fin 3)) = ∑ p : Column h, columnV k p := by
  classical
  rw [Nat.card_congr (coloringEquiv h k), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← (Fin.consEquiv (fun _ : Fin (k+1) => Column h)).sum_comp, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun p _ => tail_count k p)

def classB (p : Column 1) : Fin 2 := if p 0 = p 1 then 0 else 1
def B : Fin 2 → Fin 2 → ℕ := ![![2,2],![1,0]]
def vB : ℕ → Fin 2 → ℕ
  | 0, _ => 1
  | k+1, i => ∑ j, B i j * vB k j

/-- Class 3 is the all-distinct isolated column, retained in the domain. -/
def classH (p : Column 2) : Fin 4 :=
  if p 0 = p 1 ∧ p 1 = p 2 then 0 else
  if p 0 = p 1 ∨ p 1 = p 2 then 1 else if p 0 = p 2 then 2 else 3
def H : Fin 3 → Fin 3 → ℕ := ![![2,4,2],![1,1,0],![1,0,0]]
def Hfull : Fin 4 → Fin 4 → ℕ :=
  ![![2,4,2,0],![1,1,0,0],![1,0,0,0],![0,0,0,0]]
def hV : ℕ → Fin 3 → ℕ
  | 0, _ => 1
  | k+1, i => ∑ j, H i j * hV k j
def vH : ℕ → Fin 4 → ℕ
  | 0, _ => 1
  | k+1, i => ∑ j, Hfull i j * vH k j

set_option maxRecDepth 100000 in
theorem column_certificate :
    (∀ p : Column 1, ∀ j : Fin 2,
      (∑ q : Column 1, if cross p q ∧ classB q = j then 1 else 0) = B (classB p) j) ∧
    (∀ p : Column 2, ∀ j : Fin 4,
      (∑ q : Column 2, if cross p q ∧ classH q = j then 1 else 0) = Hfull (classH p) j) ∧
    (∀ j : Fin 2, (∑ p : Column 1, if classB p = j then 1 else 0) = (![3,6] : Fin 2 → ℕ) j) ∧
    (∀ j : Fin 4, (∑ p : Column 2, if classH p = j then 1 else 0) = (![3,12,6,6] : Fin 4 → ℕ) j) := by
  decide +kernel

private theorem class_sum {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : α → Prop) [DecidablePred P] (cl : α → ι) (w : ι → ℕ) :
    (∑ a, if P a then w (cl a) else 0) =
      ∑ j, (∑ a, if P a ∧ cl a = j then 1 else 0) * w j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P a <;> simp [hp]

private theorem continuation_B (k : ℕ) (p : Column 1) : columnV k p = vB k (classB p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [columnV,ih]
    rw [class_sum, vB]
    exact Finset.sum_congr rfl (fun j _ => by rw [column_certificate.1 p j])

private theorem continuation_H (k : ℕ) (p : Column 2) : columnV k p = vH k (classH p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [columnV,ih]
    rw [class_sum, vH]
    exact Finset.sum_congr rfl (fun j _ => by rw [column_certificate.2.1 p j])

private theorem vH_restrict (k : ℕ) (i : Fin 3) : vH k i.castSucc = hV k i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    fin_cases i <;> simp [vH,hV,Hfull,H,Fin.sum_univ_succ, ← ih]

/-- Actual all-width B and H interpretations, including the six isolated single columns. -/
theorem column_result (k : ℕ) :
    Nat.card ((stripGraph true 1 k).Coloring (Fin 3)) = 3*vB k 0 + 6*vB k 1 ∧
    Nat.card ((stripGraph true 2 k).Coloring (Fin 3)) =
      3*hV k 0 + 12*hV k 1 + 6*hV k 2 + (if k=0 then 6 else 0) := by
  have isolated : vH k 3 = if k=0 then 1 else 0 := by
    cases k with
    | zero => rfl
    | succ k => simp [vH,Hfull,Fin.sum_univ_succ]
  refine ⟨?_,?_⟩
  · rw [graph_count]
    simp only [continuation_B]
    calc
      _ = ∑ j : Fin 2, (∑ p : Column 1, if classB p = j then 1 else 0) * vB k j := by
        simpa using class_sum (fun _ : Column 1 => True) classB (vB k)
      _ = _ := by simp [column_certificate.2.2.1,Fin.sum_univ_succ]
  · rw [graph_count]
    simp only [continuation_H]
    calc
      _ = ∑ j : Fin 4, (∑ p : Column 2, if classH p = j then 1 else 0) * vH k j := by
        simpa using class_sum (fun _ : Column 2 => True) classH (vH k)
      _ = _ := by
        simp only [column_certificate.2.2.2]
        simp [Fin.sum_univ_succ,isolated,
          show vH k 0 = hV k 0 from vH_restrict k 0,
          show vH k 1 = hV k 1 from vH_restrict k 1,
          show vH k 2 = hV k 2 from vH_restrict k 2]
        split_ifs <;> omega

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
