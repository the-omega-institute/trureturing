/- GID: D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three-column array counts satisfy the recurrence and formal generating identity. -/
/-
result: proof_shape: content; escape_witness: none.
admission_basis: open-problem-resolution (#23890; Proved).
Direct frozen dependencies: HardinBarkerA209723EdgeDifferences.DistinctClockwise
  (declaration identity pending the Stage-B scoped report).
The array predicate inlines the source's signed integer difference list; proofs use
HardinBarkerA209723EdgeDifferences.DistinctClockwise, with the correspondence
checked inside arrayWalkEquiv. No duplicate predicate or type alias is introduced.
count_histories: proof_shape: content; consumers: source_count.
step_sum: proof_shape: bind-only; consumers: u_recurrence, source_count.
u_recurrence: proof_shape: content; consumers: a_recurrence.
compatibility: proof_shape: bind-only; consumers: arrayWalkEquiv.
source_count: proof_shape: content; consumers: a_recurrence, a_initial.
a_recurrence: proof_shape: content; consumers: series_formula, result.
a_initial: proof_shape: bind-only; consumers: series_formula.
series_formula: proof_shape: content; consumers: result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25560
No helper is an admission escape witness; the settling result supplies the basis.
-/
import D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences

/-! The three-column source arrays and their all-length counting proof. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences

private theorem count_histories {V : Type} [Fintype V]
    (R : V → V → Prop) [DecidableRel R]
    (u : ℕ → V → ℕ) (h0 : ∀ i, u 0 i = 1)
    (hs : ∀ n i, u (n+1) i = ∑ j, if R i j then u n j else 0) (n : ℕ) :
    Nat.card {s : Fin (n+1) → V // ∀ k : Fin n, R (s k.castSucc) (s k.succ)} =
      ∑ i, u n i := by
  classical
  let sequences (n : ℕ) : Finset (Fin (n + 1) → V) :=
    Finset.univ.filter (fun s => ∀ k : Fin n, R (s k.castSucc) (s k.succ))
  let starts (n : ℕ) (i : V) := (sequences n).filter (fun s => s 0 = i)
  have mem_sequences (n : ℕ) (s : Fin (n+1) → V) :
      s ∈ sequences n ↔ ∀ k : Fin n, R (s k.castSucc) (s k.succ) := by
    simp [sequences]
  have mem_starts (n : ℕ) (i : V) (s : Fin (n+1) → V) :
      s ∈ starts n i ↔ (∀ k : Fin n, R (s k.castSucc) (s k.succ)) ∧ s 0 = i := by
    simp [starts, mem_sequences]
  have starts_zero (i : V) : (starts 0 i).card = 1 := by
    have heq : starts 0 i = {fun _ : Fin 1 => i} := by
      apply Finset.ext
      intro s
      rw [mem_starts, Finset.mem_singleton]
      constructor
      · intro h
        funext k
        simpa only [Fin.eq_zero k] using h.2
      · rintro rfl
        exact ⟨fun k => Fin.elim0 k, rfl⟩
    rw [heq, Finset.card_singleton]
  have fiber_card (n : ℕ) (i j : V) :
      ((starts (n+1) i).filter (fun s => s 1 = j)).card =
        if R i j then (starts n j).card else 0 := by
    by_cases hij : R i j
    · rw [ite_eq_left hij]
      symm
      apply Finset.card_bij
        (s := starts n j)
        (t := (starts (n + 1) i).filter (fun s => s 1 = j))
        (fun tail _ => (Fin.cons i tail : Fin ((n+1)+1) → V))
      · intro tail htail
        rw [Finset.mem_filter]
        have ht := (mem_starts n j tail).1 htail
        refine ⟨(mem_starts (n+1) i (Fin.cons i tail)).2 ⟨?_, ?_⟩, ?_⟩
        · intro k
          refine Fin.cases ?_ (fun l => ?_) k
          · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ht.2] using hij
          · simpa only [Fin.castSucc_succ, Fin.cons_succ] using ht.1 l
        · simp only [Fin.cons_zero]
        · simpa only [← Fin.succ_zero_eq_one, Fin.cons_succ] using ht.2
      · intro t₁ _ t₂ _ h
        simpa only [Fin.tail_cons] using congrArg Fin.tail h
      · intro s hs
        have hh := Finset.mem_filter.mp hs
        have hstart := (mem_starts (n+1) i s).1 hh.1
        refine ⟨Fin.tail s, ?_, ?_⟩
        · apply (mem_starts n j (Fin.tail s)).2
          refine ⟨?_, ?_⟩
          · intro k
            simpa only [Fin.tail, Fin.succ_castSucc] using hstart.1 k.succ
          · simpa only [Fin.tail, Fin.succ_zero_eq_one] using hh.2
        · simpa only [hstart.2] using Fin.cons_self_tail s
    · have hempty : (starts (n+1) i).filter (fun s => s 1 = j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hh
        have hh := Finset.mem_filter.mp hh
        have hh' := (mem_starts (n+1) i s).1 hh.1
        apply hij
        simpa only [Fin.castSucc_zero, hh'.2, Fin.succ_zero_eq_one, hh.2] using
          hh'.1 (0 : Fin (n+1))
      rw [hempty, Finset.card_empty, ite_eq_right hij]
  have starts_succ (n : ℕ) (i : V) :
      (starts (n+1) i).card = ∑ j, if R i j then (starts n j).card else 0 := by
    calc
      _ = ∑ j : V, ((starts (n+1) i).filter (fun s => s 1 = j)).card := by
        simpa only using Finset.card_eq_sum_card_fiberwise
          (s := starts (n+1) i) (t := Finset.univ) (f := fun s => s 1) (by simp)
      _ = _ := Finset.sum_congr rfl (fun j _ => fiber_card n i j)
  have starts_bridge : ∀ n i, (starts n i).card = u n i := by
    intro n
    induction n with
    | zero => intro i; rw [starts_zero, h0]
    | succ n ih =>
      intro i
      rw [starts_succ, hs]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : R i j <;> simp [h, ih]
  calc
    _ = (sequences n).card := Nat.subtype_card (sequences n) (mem_sequences n)
    _ = ∑ i : V, (starts n i).card := by
      simpa only [starts] using Finset.card_eq_sum_card_fiberwise
        (s := sequences n) (t := Finset.univ) (f := fun s => s 0) (by simp)
    _ = _ := Finset.sum_congr rfl (fun i _ => starts_bridge n i)

/-- Every consecutive 2 by 2 subblock satisfies the literal local condition. -/
def IsSourceArray {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin 3) (Fin 3)) : Prop :=
  ∀ (i : Fin n) (j : Fin 2),
    [((X i.castSucc j.succ).val : ℤ) - ((X i.castSucc j.castSucc).val : ℤ),
     ((X i.succ j.succ).val : ℤ) - ((X i.castSucc j.succ).val : ℤ),
     ((X i.succ j.castSucc).val : ℤ) - ((X i.succ j.succ).val : ℤ),
     ((X i.castSucc j.castSucc).val : ℤ) - ((X i.succ j.castSucc).val : ℤ)].Pairwise (· ≠ ·)

/-- One quarter of the raw array count, initially in ℚ. Only n ≥ 1 is in the source domain. -/
noncomputable def a (n : ℕ) : ℚ :=
  (Nat.card {X : (Matrix (Fin (n + 1)) (Fin 3) (Fin 3)) // IsSourceArray X} : ℚ) / 4

/-- The ordinary generating series has zero constant coefficient and starts at index 1. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
    ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A = a n

/-- OEIS A209721 FORMULA assertions. The recurrence uses n = m+4.
The generating-function denominator has constant coefficient 1, so its
cross-multiplied form is equivalent to the quoted rational generating function.
Existence of the source series is asserted, not assumed. -/
def claim : Prop :=
  (∀ m : ℕ, a (m + 4) = a (m + 3) + 2 * a (m + 2) - 2 * a (m + 1)) ∧
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
  (∀ A : PowerSeries ℚ, IsSourceSeries A →
    A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (3 + PowerSeries.X - 5 * PowerSeries.X ^ 2))

private def Edge (r s : (Fin 3 × Fin 3 × Fin 3)) : Prop :=
  (r = (0,1,0) ∧ s = (2,0,2)) ∨
  (r = (1,2,1) ∧ s = (2,0,2)) ∨
  (r = (2,0,2) ∧ (s = (0,1,0) ∨ s = (1,2,1))) ∨
  (r = (1,0,1) ∧ s = (0,2,0)) ∨
  (r = (2,1,2) ∧ s = (0,2,0)) ∨
  (r = (0,2,0) ∧ (s = (1,0,1) ∨ s = (2,1,2))) ∨
  (r = (0,2,1) ∧ s = (1,0,2)) ∨
  (r = (1,0,2) ∧ s = (0,2,1)) ∨
  (r = (1,2,0) ∧ s = (2,0,1)) ∨
  (r = (2,0,1) ∧ s = (1,2,0))

set_option synthInstance.maxSize 256 in
private instance edgeDecidable : DecidableRel Edge := fun r s => by unfold Edge; infer_instance

private def step (v : (Fin 3 × Fin 3 × Fin 3) → ℕ) (r : (Fin 3 × Fin 3 × Fin 3)) : ℕ :=
  if r = (0,1,0) then v (2,0,2) else
  if r = (1,2,1) then v (2,0,2) else
  if r = (2,0,2) then v (0,1,0) + v (1,2,1) else
  if r = (1,0,1) then v (0,2,0) else
  if r = (2,1,2) then v (0,2,0) else
  if r = (0,2,0) then v (1,0,1) + v (2,1,2) else
  if r = (0,2,1) then v (1,0,2) else
  if r = (1,0,2) then v (0,2,1) else
  if r = (1,2,0) then v (2,0,1) else
  if r = (2,0,1) then v (1,2,0) else 0

private def u : ℕ → (Fin 3 × Fin 3 × Fin 3) → ℕ
  | 0 => fun _ => 1
  | n+1 => step (u n)

private theorem step_sum (v : (Fin 3 × Fin 3 × Fin 3) → ℕ) (r : (Fin 3 × Fin 3 × Fin 3)) :
    step v r = ∑ s : (Fin 3 × Fin 3 × Fin 3), if Edge r s then v s else 0 := by
  rcases r with ⟨a,b,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [step, Edge, Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem u_recurrence : ∀ n r,
    u (n+4) r + 2*u (n+1) r = u (n+3) r + 2*u (n+2) r := by
  intro n
  induction n with
  | zero =>
    rintro ⟨a,b,c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  | succ n ih =>
    intro r
    simp only [show ∀ k, u (k+1) r = ∑ s : (Fin 3 × Fin 3 × Fin 3), if Edge r s then u k s else 0
      from fun k => step_sum (u k) r]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : Edge r s
    · simpa only [h, ite_true] using ih s
    · simp only [h, ite_false, mul_zero, add_zero]

private theorem compatibility (r s : Fin 3 × Fin 3 × Fin 3) :
    (∀ j : Fin 2, D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences.DistinctClockwise
      (![r.1, r.2.1, r.2.2] j.castSucc) (![r.1, r.2.1, r.2.2] j.succ)
      (![s.1, s.2.1, s.2.2] j.castSucc) (![s.1, s.2.1, s.2.2] j.succ)) ↔ Edge r s := by
  unfold D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences.DistinctClockwise
  revert r s
  decide

private def arrayWalkEquiv (n : ℕ) :
    {X : Matrix (Fin (n + 1)) (Fin 3) (Fin 3) // IsSourceArray X} ≃
      {s : Fin (n+1) → (Fin 3 × Fin 3 × Fin 3) // ∀ k : Fin n, Edge (s k.castSucc) (s k.succ)} := by
  let e := (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 3)) (finTwoArrowEquiv (Fin 3)))
  have he (r : Fin 3 × Fin 3 × Fin 3) : e.symm r = ![r.1, r.2.1, r.2.2] := by
    exact (Equiv.symm_apply_eq e).mpr rfl
  refine (Equiv.piCongrRight (fun _ : Fin (n+1) => e)).subtypeEquiv ?_
  intro X
  change IsSourceArray X ↔ ∀ k : Fin n, Edge (e (X k.castSucc)) (e (X k.succ))
  unfold IsSourceArray
  apply forall_congr'
  intro k
  have h := compatibility (e (X k.castSucc)) (e (X k.succ))
  simpa only [← he, Equiv.symm_apply_apply, D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences.DistinctClockwise] using h

private theorem source_count (n : ℕ) :
    Nat.card {X : (Matrix (Fin (n + 1)) (Fin 3) (Fin 3)) // IsSourceArray X} = ∑ r : (Fin 3 × Fin 3 × Fin 3), u n r := by
  rw [Nat.card_congr (arrayWalkEquiv n)]
  exact count_histories Edge u (fun _ => rfl) (fun n r => step_sum (u n) r) n

private theorem a_recurrence (n : ℕ) :
    a (n+4) = a (n+3) + 2*a (n+2) - 2*a (n+1) := by
  have h : (∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+4) r) + 2*(∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+1) r) =
      (∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+3) r) + 2*(∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+2) r) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => u_recurrence n r)
  have hc : ((∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+4) r) : ℚ) + 2*((∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+1) r) : ℚ) =
      ((∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+3) r) : ℚ) + 2*((∑ r : (Fin 3 × Fin 3 × Fin 3), u (n+2) r) : ℚ) := by
    exact_mod_cast h
  simp only [a, source_count]
  push_cast
  linarith

private theorem a_initial : a 1 = 3 ∧ a 2 = 4 ∧ a 3 = 5 := by
  simp only [a, source_count]
  norm_num [u, step, Fintype.sum_prod_type, Fin.sum_univ_succ]

open PowerSeries

private theorem series_formula (A : PowerSeries ℚ) (hA : IsSourceSeries A) :
    A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (3 + PowerSeries.X - 5 * PowerSeries.X ^ 2) := by
  have expand :
      A * ((1-X)*(1-2*X^2)) = A - A*X^1 - 2*(A*X^2) + 2*(A*X^3) := by ring
  have numer :
      X*(3+X-5*X^2 : PowerSeries ℚ) = C 3*X^1 + C 1*X^2 - C 5*X^3 := by
    simp only [map_ofNat, map_one]
    ring
  rw [expand, numer]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C]
  rcases a_initial with ⟨h1,h2,h3⟩
  rcases n with _ | _ | _ | _ | n
  · norm_num [hA.1]
  · norm_num [hA.1, hA.2 1 (by decide), h1]
  · norm_num [hA.1, hA.2 1 (by decide), hA.2 2 (by decide), h1, h2]
  · norm_num [hA.1, hA.2 1 (by decide), hA.2 2 (by decide), hA.2 3 (by decide), h1, h2, h3]
  · simp only [show 1 ≤ n+4 by omega, show 2 ≤ n+4 by omega,
      show 3 ≤ n+4 by omega, ite_true,
      show n+4-1 = n+3 by omega, show n+4-2 = n+2 by omega,
      show n+4-3 = n+1 by omega]
    rw [hA.2 (n+4) (by omega), hA.2 (n+3) (by omega),
      hA.2 (n+2) (by omega), hA.2 (n+1) (by omega)]
    simp
    linarith [a_recurrence n]

theorem result : claim := by
  refine ⟨a_recurrence, ?_, series_formula⟩
  refine ⟨PowerSeries.mk (fun n => if n = 0 then 0 else a n), ?_, ?_⟩
  · simp [PowerSeries.coeff_mk]
  · intro n hn
    simp [PowerSeries.coeff_mk, show n ≠ 0 by omega]

end D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences
