/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal positive-height arrays and their exact scanner-weighted pair transfer. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200LiteralBridge

/-! The labelled transfer retains every individual-colour scanner fibre. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer

open HardinA233196Strip (Seen good finish)
open HardinA233196Strip (beta)
open HardinA233196Strip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233200LiteralBridge (rowWeight rowFinish scanner_fibres)

abbrev Row := Fin 6 → Fin 8
abbrev PairRow := Fin 6 → Fin 4
abbrev Boundary := Fin 6 → Fin 4

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 5, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 7

def bonds (c d : Row) : Prop :=
  (∀ j : Fin 6, c j ≠ d j ∧ (c j).val + (d j).val ≠ 7) ∧
    (∀ j : Fin 5, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 7)

def rho {h : ℕ} (p : Fin h × Fin 6) : ℕ := 6 * p.1.val + p.2.val

def Legal {h : ℕ} (A : Fin h × Fin 6 → Fin 8) : Prop :=
  (∃ i : Fin h, i.val = 0 ∧ A (i, 0) = 0) ∧
  (∀ i, rowLegal (fun j => A (i, j))) ∧
  (∀ (i : Fin h) (hi : i.val + 1 < h),
    bonds (fun j => A (i, j)) (fun j => A (⟨i.val + 1, hi⟩, j))) ∧
  (∀ i j,
    ((A (i, j) = 2 ∨ A (i, j) = 3 ∨ A (i, j) = 4 ∨ A (i, j) = 5 ∨ A (i, j) = 6) →
      ∃ q, rho q < rho (i, j) ∧ A q = 1) ∧
    ((A (i, j) = 3 ∨ A (i, j) = 4 ∨ A (i, j) = 5) →
      ∃ q, rho q < rho (i, j) ∧ A q = 2) ∧
    (A (i, j) = 4 → ∃ q, rho q < rho (i, j) ∧ A q = 3))

private theorem prior_rho {h : ℕ} (A : Fin h × Fin 6 → Fin 8)
    (i : Fin h) (j : Fin 6) (d : Fin 8) :
    HardinA233196Strip.prior (fun r k => A (r, k)) i j d ↔
      ∃ q, rho q < rho (i, j) ∧ A q = d := by
  unfold HardinA233196Strip.prior rho
  constructor
  · rintro ⟨r, k, hr, hd⟩
    refine ⟨(r, k), ?_, hd⟩
    change 6 * r.val + k.val < 6 * i.val + j.val
    have hk := k.isLt
    have hj := j.isLt
    rcases hr with hr | ⟨rfl, hr⟩ <;> change _ < _ at hr <;> omega
  · rintro ⟨⟨r, k⟩, hr, hd⟩
    change 6 * r.val + k.val < 6 * i.val + j.val at hr
    refine ⟨r, k, ?_, hd⟩
    have hk := k.isLt
    have hj := j.isLt
    by_cases he : r = i
    · right; refine ⟨he, ?_⟩; subst r; omega
    · left; have hne : r.val ≠ i.val := fun h => he (Fin.ext h); omega

private theorem legal_iff {h : ℕ} (A : Fin h × Fin 6 → Fin 8) :
    Legal A ↔ widthLegal rowLegal bonds A := by
  simp only [Legal, widthLegal, HardinA233196Strip.widthNormal, Bool.false_eq_true,
    false_or, prior_rho]


private instance decidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((∀ _, _ ∧ _) ∧ (∀ _, _ ∧ _)))

private instance decidableLegal {h : ℕ} (A : Fin h × Fin 6 → Fin 8) : Decidable (Legal A) :=
  decidable_of_iff (widthLegal rowLegal bonds A) (legal_iff A).symm

/-- The original individual-array count, on the positive source domain only. -/
def a (h : ℕ+) : ℕ := (Finset.univ.filter (fun A : Fin h.val × Fin 6 → Fin 8 => Legal A)).card

def pairs (c : Row) : Boundary := fun j => beta (c j)
def compatible (p : Boundary) (c : Row) : Prop := (∀ j : Fin 6, p j ≠ beta (c j)) ∧
  (∀ j : Fin 5, p j.succ ≠ beta (c j.castSucc))
private instance decidableCompatible (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable ((∀ _, _) ∧ (∀ _, _)))

def rowProper (q : PairRow) : Prop := ∀ j : Fin 5, q j.castSucc ≠ q j.succ
def labelCompatible (p : Boundary) (q : PairRow) : Prop := (∀ j : Fin 6, p j ≠ q j) ∧
  (∀ j : Fin 5, p j.succ ≠ q j.castSucc)
def labelBoundary (q : PairRow) : Boundary := q
private instance decidableRowProper (q : PairRow) : Decidable (rowProper q) :=
  inferInstanceAs (Decidable (∀ _, _))
private instance decidableLabelCompatible (p : Boundary) (q : PairRow) :
    Decidable (labelCompatible p q) := inferInstanceAs (Decidable ((∀ _, _) ∧ (∀ _, _)))

def pairV : ℕ → Seen → Boundary → ℤ
  | 0, _, _ => 1
  | n + 1, s, p => ∑ q : PairRow, if rowProper q ∧ labelCompatible p q then
      rowWeight s q * pairV n (rowFinish s q) (labelBoundary q) else 0

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private theorem step_pair (w : Seen → Boundary → ℤ) (s : Seen) (p : Boundary) :
    widthStep rowLegal pairs compatible w s p =
      ∑ q : PairRow, if rowProper q ∧ labelCompatible p q then
        rowWeight s q * w (rowFinish s q) (labelBoundary q) else 0 := by
  unfold widthStep
  have h := scanner_fibres 6 s (fun t q =>
    if rowProper q ∧ labelCompatible p q then w t (labelBoundary q) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro c _
    have hr : rowProper (fun j => beta (c j)) ↔ rowLegal c := by
      simp only [rowProper, rowLegal, colour_bond_iff]
    have hc : labelCompatible p (fun j => beta (c j)) ↔ compatible p c := Iff.rfl
    have hb : labelBoundary (fun j => beta (c j)) = pairs c := rfl
    simp only [hr, hc, hb]
    by_cases hg : good s c <;> by_cases hl : rowLegal c ∧ compatible p c <;>
      simp only [hg, hl, ite_true, ite_false, and_true, and_false]
  · apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp_all

/-- All continuation heights retain the exact original scanner and individual-colour fibres. -/
theorem continuation_pair_bridge (n : ℕ) (s : Seen) (p : Boundary) :
    widthV rowLegal pairs compatible n s p = pairV n s p := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [widthV, step_pair]
    simp_rw [ih]
    rfl

private theorem literal_colour_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
        pairV n (finish (false, false, false) c) (pairs c) else 0 := by
  have h := width_counting_bridge rowLegal pairs compatible bonds bonds_iff n
  change ((Finset.univ.filter (fun A : Fin (n + 1) × Fin 6 → Fin 8 =>
    widthLegal rowLegal bonds A)).card : ℤ) = _ at h
  have ha : (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) = widthTotal rowLegal pairs
      (widthV rowLegal pairs compatible n) := by
    have hf : (Finset.univ.filter (fun A : Fin (n + 1) × Fin 6 → Fin 8 => Legal A)) =
        (Finset.univ.filter (fun A => widthLegal rowLegal bonds A)) := by
      apply Finset.filter_congr
      intro A _
      exact legal_iff A
    change ((Finset.univ.filter (fun A : Fin (n + 1) × Fin 6 → Fin 8 => Legal A)).card : ℤ) = _
    rw [hf]
    exact h
  rw [ha]
  unfold widthTotal
  simp_rw [continuation_pair_bridge]

private theorem first_fibres (H : Seen → PairRow → ℤ) :
    (∑ c : Row, if c 0 = 0 ∧ good (false, false, false) c then
      H (finish (false, false, false) c) (fun j => beta (c j)) else 0) =
    ∑ q : Fin 5 → Fin 4, rowWeight (false, false, false) q *
      H (rowFinish (false, false, false) q) (Fin.cons 0 q) := by
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 8)).sum_comp, Fintype.sum_prod_type]
  change (∑ x : Fin 8, ∑ c : Fin 5 → Fin 8,
    if x = 0 ∧ good (false, false, false) (Fin.cons x c) then
      H (finish (false, false, false) (Fin.cons x c))
        (fun j => beta ((Fin.cons x c : Row) j)) else 0) = _
  rw [Finset.sum_eq_single (0 : Fin 8)]
  · have hh := scanner_fibres 5 (false, false, false)
      (fun t q => H t (Fin.cons 0 q))
    convert hh using 1
    apply Finset.sum_congr rfl
    intro c _
    have hb : (fun j => beta ((Fin.cons 0 c : Row) j)) =
        Fin.cons 0 (fun j => beta (c j)) := Fin.comp_cons beta 0 c
    have ha : HardinA233196Strip.allowed (false, false, false) (0 : Fin 8) := by decide +kernel
    have hadv : HardinA233196Strip.advance (false, false, false) (0 : Fin 8) =
        (false, false, false) := by decide +kernel
    have hg : good (false, false, false) (Fin.cons 0 c) ↔ good (false, false, false) c := by
      change (HardinA233196Strip.allowed (false, false, false) 0 ∧
        good (HardinA233196Strip.advance (false, false, false) 0) c) ↔ good (false, false, false) c
      rw [hadv]
      simp only [ha, true_and]
    have hf : finish (false, false, false) (Fin.cons 0 c) = finish (false, false, false) c := by
      change finish (HardinA233196Strip.advance (false, false, false) 0) c = _
      rw [hadv]
    simp only [hg, hf, hb, eq_self, true_and]
  · intro x _ hx
    simp [hx]
  · simp

/-- The original literal count is an exact scanner-weighted sum on labelled pair rows. -/
theorem literal_pair_bridge (n : ℕ) :
    (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ q : Fin 5 → Fin 4, if rowProper (Fin.cons 0 q) then
        rowWeight (false, false, false) q *
          pairV n (rowFinish (false, false, false) q) (Fin.cons 0 q) else 0 := by
  rw [literal_colour_bridge]
  have h := first_fibres (fun t q =>
    if rowProper q then pairV n t (labelBoundary q) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro c _
    have hr : rowProper (fun j => beta (c j)) ↔ rowLegal c := by
      simp only [rowProper, rowLegal, colour_bond_iff]
    have hb : labelBoundary (fun j => beta (c j)) = pairs c := rfl
    simp only [hr, hb]
    by_cases h0 : c 0 = 0 <;> by_cases hg : good (false, false, false) c <;>
      by_cases hl : rowLegal c <;> simp [h0, hg, hl]
  · apply Finset.sum_congr rfl
    intro q _
    have hb : labelBoundary (Fin.cons 0 q) = Fin.cons 0 q := rfl
    simp only [hb]
    split_ifs <;> simp_all



open HardinA233200LiteralBridge (labelAdvance labelWeight)

def seen (k : Fin 4) : Seen :=
  (decide (1 ≤ k.val), decide (2 ≤ k.val), decide (3 ≤ k.val))
private def containsKnown (k : Fin 4) (s : Seen) : Prop :=
  (1 ≤ k.val → s.1 = true) ∧ (2 ≤ k.val → s.2.1 = true) ∧
    (3 ≤ k.val → s.2.2 = true)
private instance (k : Fin 4) (s : Seen) : Decidable (containsKnown k s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private def fixes (k : Fin 4) (e : Equiv.Perm (Fin 4)) : Prop :=
  ∀ x, k.val < x.val → e x = x
private instance (k : Fin 4) (e : Equiv.Perm (Fin 4)) : Decidable (fixes k e) :=
  inferInstanceAs (Decidable (∀ _, _))

private theorem known_cell : ∀ (k : Fin 4) (s : Seen) (q : Fin 4),
    containsKnown k s → q.val ≤ k.val →
    labelAdvance s q = s ∧ labelWeight s q = 2 := by
  unfold containsKnown
  decide +kernel

private theorem preserves_known : ∀ (k : Fin 4) (s : Seen) (q : Fin 4),
    containsKnown k s → containsKnown k (labelAdvance s q) := by
  unfold containsKnown
  decide +kernel

private theorem cell_equiv (k : Fin 4) (s : Seen) (e : Equiv.Perm (Fin 4))
    (hs : containsKnown k s) (he : fixes k e) (q : Fin 4) :
    labelAdvance s (e q) = labelAdvance s q ∧
      labelWeight s (e q) = labelWeight s q ∧ containsKnown k (labelAdvance s q) := by
  refine ⟨?_, ?_, preserves_known k s q hs⟩
  all_goals
    by_cases hq : q.val ≤ k.val
    · have heq : (e q).val ≤ k.val := by
        by_contra h
        have hh := he (e q) (by omega)
        have hh' : e q = q := e.injective hh
        rw [hh'] at h
        exact h hq
      first
      | exact (known_cell k s (e q) hs heq).1.trans (known_cell k s q hs hq).1.symm
      | exact (known_cell k s (e q) hs heq).2.trans (known_cell k s q hs hq).2.symm
    · rw [he q (by omega)]

private theorem row_equiv (k : Fin 4) (s : Seen) (e : Equiv.Perm (Fin 4))
    (hs : containsKnown k s) (he : fixes k e) (d : ℕ) (q : Fin d → Fin 4) :
    rowFinish s (fun j => e (q j)) = rowFinish s q ∧
      rowWeight s (fun j => e (q j)) = rowWeight s q ∧ containsKnown k (rowFinish s q) := by
  induction d generalizing s with
  | zero => exact ⟨rfl, rfl, hs⟩
  | succ d ih =>
    have hc := cell_equiv k s e hs he (q 0)
    have ht : Fin.tail (fun j : Fin (d+1) => e (q j)) =
        (fun j : Fin d => e (Fin.tail q j)) := by funext j; rfl
    simp only [rowFinish, rowWeight, hc.1, hc.2.1, ht]
    have hr := ih _ hc.2.2 (Fin.tail q)
    exact ⟨hr.1, congrArg (fun x => labelWeight s (q 0) * x) hr.2.1, hr.2.2⟩

private theorem permutation_invariant (n : ℕ) (k : Fin 4) (s : Seen)
    (e : Equiv.Perm (Fin 4)) (hs : containsKnown k s) (he : fixes k e) (p : Boundary) :
    pairV n s (fun j => e (p j)) = pairV n s p := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [pairV, pairV]
    let E : PairRow ≃ PairRow := Equiv.arrowCongr (Equiv.refl (Fin 6)) e
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    change (if rowProper (fun j => e (q j)) ∧
      labelCompatible (fun j => e (p j)) (fun j => e (q j)) then
      rowWeight s (fun j => e (q j)) * pairV n (rowFinish s (fun j => e (q j)))
        (fun j => e (q j)) else 0) = _
    have h := row_equiv k s e hs he 6 q
    simp only [rowProper, labelCompatible, e.injective.ne_iff, h.1, h.2.1]
    rw [ih _ h.2.2]
    rfl

private def third (p : Boundary) : Fin 4 :=
  if p 2 ≠ p 0 ∧ p 2 ≠ p 1 then p 2
  else if p 3 ≠ p 0 ∧ p 3 ≠ p 1 then p 3
  else if p 4 ≠ p 0 ∧ p 4 ≠ p 1 then p 4
  else if p 5 ≠ p 0 ∧ p 5 ≠ p 1 then p 5
  else if (0 : Fin 4) ≠ p 0 ∧ (0 : Fin 4) ≠ p 1 then 0
  else if (1 : Fin 4) ≠ p 0 ∧ (1 : Fin 4) ≠ p 1 then 1 else 2
private def relabel (p : Boundary) (x : Fin 4) : Fin 4 :=
  if x = p 0 then 0 else if x = p 1 then 1 else if x = third p then 2 else 3
private def normalize (p : Boundary) : Boundary := fun j => relabel p (p j)
private def used (k : Fin 4) (p : Boundary) : Prop := ∀ j, (p j).val ≤ k.val
private instance (k : Fin 4) (p : Boundary) : Decidable (used k p) :=
  inferInstanceAs (Decidable (∀ _, _))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel checks the complete finite state telescope.
private theorem relabel_spec : ∀ p : Boundary, rowProper p →
    Function.Bijective (relabel p) ∧
      ∀ k : Fin 4, used k p → ∀ x : Fin 4, k.val < x.val → relabel p x = x := by
  decide +kernel

private noncomputable def normalizer (p : Boundary) (hp : rowProper p) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (relabel p) (relabel_spec p hp).1

/-- Historical stages and canonical proper six-cell boundaries. -/
def nativeStage : Fin 58 → Fin 4 :=
  ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

def nativeRepresentative : Fin 58 → Boundary :=
  ![![0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 2],
    ![0, 1, 0, 1, 2, 0],
    ![0, 1, 0, 1, 2, 1],
    ![0, 1, 0, 2, 0, 1],
    ![0, 1, 0, 2, 0, 2],
    ![0, 1, 0, 2, 1, 0],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 2, 0, 1, 0],
    ![0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 0, 2, 0],
    ![0, 1, 2, 0, 2, 1],
    ![0, 1, 2, 1, 0, 1],
    ![0, 1, 2, 1, 0, 2],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 2, 1, 2, 1],
    ![0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 2],
    ![0, 1, 0, 1, 2, 0],
    ![0, 1, 0, 1, 2, 1],
    ![0, 1, 0, 1, 2, 3],
    ![0, 1, 0, 2, 0, 1],
    ![0, 1, 0, 2, 0, 2],
    ![0, 1, 0, 2, 0, 3],
    ![0, 1, 0, 2, 1, 0],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 0, 2, 1, 3],
    ![0, 1, 0, 2, 3, 0],
    ![0, 1, 0, 2, 3, 1],
    ![0, 1, 0, 2, 3, 2],
    ![0, 1, 2, 0, 1, 0],
    ![0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 0, 1, 3],
    ![0, 1, 2, 0, 2, 0],
    ![0, 1, 2, 0, 2, 1],
    ![0, 1, 2, 0, 2, 3],
    ![0, 1, 2, 0, 3, 0],
    ![0, 1, 2, 0, 3, 1],
    ![0, 1, 2, 0, 3, 2],
    ![0, 1, 2, 1, 0, 1],
    ![0, 1, 2, 1, 0, 2],
    ![0, 1, 2, 1, 0, 3],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 2, 1, 2, 1],
    ![0, 1, 2, 1, 2, 3],
    ![0, 1, 2, 1, 3, 0],
    ![0, 1, 2, 1, 3, 1],
    ![0, 1, 2, 1, 3, 2],
    ![0, 1, 2, 3, 0, 1],
    ![0, 1, 2, 3, 0, 2],
    ![0, 1, 2, 3, 0, 3],
    ![0, 1, 2, 3, 1, 0],
    ![0, 1, 2, 3, 1, 2],
    ![0, 1, 2, 3, 1, 3],
    ![0, 1, 2, 3, 2, 0],
    ![0, 1, 2, 3, 2, 1],
    ![0, 1, 2, 3, 2, 3]]

private def indexThree (p : Boundary) : Fin 16 :=
  if p 2 = 0 then if p 3 = 1 then if p 4 = 0 then if p 5 = 1 then 0 else 1 else if p 5 = 0 then 2 else 3 else if p 4 = 0 then if p 5 = 1 then 4 else 5 else if p 5 = 0 then 6 else 7 else if p 3 = 0 then if p 4 = 1 then if p 5 = 0 then 8 else 9 else if p 5 = 0 then 10 else 11 else if p 4 = 0 then if p 5 = 1 then 12 else 13 else if p 5 = 0 then 14 else 15

private def indexFour (p : Boundary) : Fin 41 :=
  if p 2 = 0 then if p 3 = 1 then if p 4 = 0 then if p 5 = 1 then 0 else 1 else if p 5 = 0 then 2 else if p 5 = 1 then 3 else 4 else if p 4 = 0 then if p 5 = 1 then 5 else if p 5 = 2 then 6 else 7 else if p 4 = 1 then if p 5 = 0 then 8 else if p 5 = 2 then 9 else 10 else if p 5 = 0 then 11 else if p 5 = 1 then 12 else 13 else if p 3 = 0 then if p 4 = 1 then if p 5 = 0 then 14 else if p 5 = 2 then 15 else 16 else if p 4 = 2 then if p 5 = 0 then 17 else if p 5 = 1 then 18 else 19 else if p 5 = 0 then 20 else if p 5 = 1 then 21 else 22 else if p 3 = 1 then if p 4 = 0 then if p 5 = 1 then 23 else if p 5 = 2 then 24 else 25 else if p 4 = 2 then if p 5 = 0 then 26 else if p 5 = 1 then 27 else 28 else if p 5 = 0 then 29 else if p 5 = 1 then 30 else 31 else if p 4 = 0 then if p 5 = 1 then 32 else if p 5 = 2 then 33 else 34 else if p 4 = 1 then if p 5 = 0 then 35 else if p 5 = 2 then 36 else 37 else if p 5 = 0 then 38 else if p 5 = 1 then 39 else 40

/-- Canonical class with the complete historical scanner nativeStage retained. -/
def nativeClassOf (k : Fin 4) (p : Boundary) : Fin 58 :=
  if k = 1 then 0 else if k = 2 then ⟨1 + (indexThree (normalize p)).val, by omega⟩
  else ⟨17 + (indexFour (normalize p)).val, by omega⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel checks the complete finite state telescope.
private theorem class_spec : ∀ (k : Fin 4) (p : Boundary), 1 ≤ k.val →
    rowProper p → used k p →
    nativeStage (nativeClassOf k p) = k ∧ nativeRepresentative (nativeClassOf k p) = normalize p := by
  decide +kernel


private theorem canonical_bridge (n : ℕ) (k : Fin 4) (p : Boundary)
    (hk : 1 ≤ k.val) (hp : rowProper p) (hu : used k p) :
    pairV n (seen k) (nativeRepresentative (nativeClassOf k p)) = pairV n (seen k) p := by
  rw [(class_spec k p hk hp hu).2]
  exact permutation_invariant n k (seen k) (normalizer p hp)
    (by fin_cases k <;> decide +kernel) ((relabel_spec p hp).2 k hu) p

def finalStage (s : Seen) : Fin 4 :=
  if s.2.2 then 3 else if s.2.1 then 2 else if s.1 then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel checks the complete finite state telescope.
private theorem successor_spec : ∀ (k : Fin 4) (q : PairRow), 1 ≤ k.val →
    rowProper q → rowWeight (seen k) q ≠ 0 →
      1 ≤ (finalStage (rowFinish (seen k) q)).val ∧
      rowFinish (seen k) q = seen (finalStage (rowFinish (seen k) q)) ∧
      used (finalStage (rowFinish (seen k) q)) q := by
  unfold rowProper used
  decide +kernel

/-- Every entry is the exact weighted fibre of proper compatible next rows. -/
def nativeT : Matrix (Fin 58) (Fin 58) ℤ := fun i j =>
  ∑ q : PairRow, if rowProper q ∧ labelCompatible (nativeRepresentative i) q ∧
      nativeClassOf (finalStage (rowFinish (seen (nativeStage i)) q)) q = j then
    rowWeight (seen (nativeStage i)) q else 0

private theorem T_mulVec (v : Fin 58 → ℤ) (i : Fin 58) :
    nativeT.mulVec v i = ∑ q : PairRow,
      if rowProper q ∧ labelCompatible (nativeRepresentative i) q then
        rowWeight (seen (nativeStage i)) q *
          v (nativeClassOf (finalStage (rowFinish (seen (nativeStage i)) q)) q) else 0 := by
  simp only [Matrix.mulVec, dotProduct, nativeT, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : rowProper q ∧ labelCompatible (nativeRepresentative i) q
  · simp [h.1, h.2]
  · simp only [show ∀ j, ¬ (rowProper q ∧ labelCompatible (nativeRepresentative i) q ∧
        nativeClassOf (finalStage (rowFinish (seen (nativeStage i)) q)) q = j) from
        fun _ hh => h ⟨hh.1, hh.2.1⟩, ite_false, zero_mul, Finset.sum_const_zero, h]

private theorem continuation (n : ℕ) (k : Fin 4) (p : Boundary)
    (hk : 1 ≤ k.val) (hp : rowProper p) (hu : used k p) :
    pairV n (seen k) p = (nativeT^n).mulVec (1 : Fin 58 → ℤ) (nativeClassOf k p) := by
  induction n generalizing k p with
  | zero => simp [pairV, Matrix.one_mulVec]
  | succ n ih =>
    rw [← canonical_bridge (n+1) k p hk hp hu, pairV,
      pow_succ', ← Matrix.mulVec_mulVec, T_mulVec, (class_spec k p hk hp hu).1]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with h
    · by_cases hz : rowWeight (seen k) q = 0
      · simp [hz]
      · have hs := successor_spec k q hk h.1 hz
        congr 1
        change pairV n (rowFinish (seen k) q) q = _
        exact (congrArg (fun t => pairV n t q) hs.2.1).trans
          (ih _ _ hs.1 h.1 hs.2.2)
    · rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel checks the complete finite state telescope.
private theorem first_spec : ∀ q : Fin 5 → Fin 4,
    rowProper (Fin.cons 0 q) → rowWeight (false, false, false) q ≠ 0 →
    1 ≤ (finalStage (rowFinish (false, false, false) q)).val ∧
    rowFinish (false, false, false) q = seen (finalStage (rowFinish (false, false, false) q)) ∧
    used (finalStage (rowFinish (false, false, false) q)) (Fin.cons 0 q) := by
  decide +kernel

/-- The first colour is fixed to zero and contributes multiplicity one. -/
def nativeInitial (i : Fin 58) : ℤ :=
  ∑ q : Fin 5 → Fin 4, if rowProper (Fin.cons 0 q) ∧
      nativeClassOf (finalStage (rowFinish (false, false, false) q)) (Fin.cons 0 q) = i then
    rowWeight (false, false, false) q else 0

/-- The exact literal count at every positive height is a 58-state matrix readout. -/
theorem native_linear_bridge (n : ℕ) :
    (a ⟨n+1, Nat.succ_pos n⟩ : ℤ) =
      dotProduct nativeInitial ((nativeT^n).mulVec (1 : Fin 58 → ℤ)) := by
  rw [literal_pair_bridge]
  have he (q : Fin 5 → Fin 4) (hq : rowProper (Fin.cons 0 q)) :
      rowWeight (false, false, false) q *
        pairV n (rowFinish (false, false, false) q) (Fin.cons 0 q) =
      rowWeight (false, false, false) q * (nativeT^n).mulVec (1 : Fin 58 → ℤ)
        (nativeClassOf (finalStage (rowFinish (false, false, false) q)) (Fin.cons 0 q)) := by
    by_cases hz : rowWeight (false, false, false) q = 0
    · simp [hz]
    · have hs := first_spec q hq hz
      congr 1
      exact (congrArg (fun t => pairV n t (Fin.cons 0 q)) hs.2.1).trans
        (continuation n _ _ hs.1 hq hs.2.2)
  simp only [dotProduct, nativeInitial, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : rowProper (Fin.cons 0 q)
  · rw [if_pos hq, he q hq]
    simp [hq]
  · simp [hq]


end D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
