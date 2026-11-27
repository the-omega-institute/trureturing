/- GID: D5/S3/Arith/Divisors/ErdosNicolas/GapChecker
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main00.chunk_checked
   digest: Prefix recurrences and sequential adjacent-gap weight certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.GapMajorant

/-! The certificate lists are traversed sequentially, with one reverse of the prefixes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Partial sums of the rounded inverse squared rank distances. -/
def gapPrefix (Q j : ℕ) : ℕ := ∑ k ∈ Ico 1 (j + 1), ceilDiv Q (k ^ 2)

private theorem gapMultiplicity_succ_balance (t r k : ℕ) (hr : r + 2 < t)
    (hk : 1 ≤ k) (hkt : k < t) :
    gapMultiplicity t (r + 1) k + (if k ≤ r + 1 then 1 else 0) =
      gapMultiplicity t r k + (if k ≤ t - r - 2 then 1 else 0) := by
  unfold gapMultiplicity
  split_ifs <;> omega

private theorem filtered_prefix (Q t c : ℕ) (hc : c < t) :
    (∑ k ∈ Ico 1 t, if k ≤ c then ceilDiv Q (k ^ 2) else 0) = gapPrefix Q c := by
  rw [← sum_filter]
  unfold gapPrefix
  congr 1
  ext k
  simp only [mem_filter, mem_Ico]
  omega

/-- Equation (25), in a subtraction-free form suitable for checking natural weights. -/
theorem gapWeight_succ_balance (Q t r : ℕ) (hr : r + 2 < t) :
    gapWeight Q t (r + 1) + gapPrefix Q (r + 1) =
      gapWeight Q t r + gapPrefix Q (t - r - 2) := by
  have hpoint (k : ℕ) (hk : k ∈ Ico 1 t) :
      gapMultiplicity t (r + 1) k * ceilDiv Q (k ^ 2) +
          (if k ≤ r + 1 then ceilDiv Q (k ^ 2) else 0) =
        gapMultiplicity t r k * ceilDiv Q (k ^ 2) +
          (if k ≤ t - r - 2 then ceilDiv Q (k ^ 2) else 0) := by
    have hm := gapMultiplicity_succ_balance t r k hr (mem_Ico.mp hk).1
      (mem_Ico.mp hk).2
    have hh := congrArg (fun v => v * ceilDiv Q (k ^ 2)) hm
    simpa only [add_mul, ite_mul, one_mul, zero_mul] using hh
  have hs := sum_congr rfl hpoint
  simp only [sum_add_distrib] at hs
  rw [filtered_prefix Q t (r + 1) (by omega),
    filtered_prefix Q t (t - r - 2) (by omega)] at hs
  exact hs

/-- The first weight is the full prefix sum. -/
theorem gapWeight_zero (Q t : ℕ) :
    gapWeight Q t 0 = gapPrefix Q (t - 1) := by
  by_cases ht : t = 0
  · simp [ht, gapWeight, gapPrefix]
  have he : t - 1 + 1 = t := by omega
  unfold gapWeight gapPrefix
  rw [he]
  apply sum_congr rfl
  intro k hk
  have hm : gapMultiplicity t 0 k = 1 := by
    unfold gapMultiplicity
    have := mem_Ico.mp hk
    omega
  simp only [hm, one_mul]

#print axioms gapWeight_succ_balance

/-- Verify each prefix using one newly rounded inverse-square term. -/
def checkGapPrefixes (Q k s : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => decide (p = s) &&
      checkGapPrefixes Q (k + 1) (s + ceilDiv Q ((k + 1) ^ 2)) ps

/-- Check the subtraction-free adjacent-weight recurrence against the prefix streams. -/
def checkGapLinks : List ℕ → List ℕ → List ℕ → Bool
  | _, _, [] => true
  | _, _, [_] => true
  | a :: as, b :: bs, w :: v :: ws =>
      decide (v + a = w + b) && checkGapLinks as bs (v :: ws)
  | _, _, _ => false

/-- The prefix list has length `t`; the weight list has length `t-1`. -/
def checkGapWeights (Q t : ℕ) (ps ws : List ℕ) : Bool :=
  decide (ps.length = t) && decide (ws.length = t - 1) &&
    checkGapPrefixes Q 0 0 ps && decide (ws.headD 0 = ps.reverse.headD 0) &&
      checkGapLinks ps.tail ps.reverse.tail ws

private theorem gapPrefix_succ (Q k : ℕ) :
    gapPrefix Q (k + 1) = gapPrefix Q k + ceilDiv Q ((k + 1) ^ 2) := by
  unfold gapPrefix
  exact sum_Ico_succ_top (by omega) _

private theorem checkGapPrefixes_sound (Q k : ℕ) (ps : List ℕ)
    (h : checkGapPrefixes Q k (gapPrefix Q k) ps = true) :
    ∀ r < ps.length, ps.getD r 0 = gapPrefix Q (k + r) := by
  induction ps generalizing k with
  | nil => simp
  | cons p ps ih =>
    simp only [checkGapPrefixes, Bool.and_eq_true, decide_eq_true_eq] at h
    intro r hr
    cases r with
    | zero => simpa using h.1
    | succ r =>
      have ht : checkGapPrefixes Q (k + 1) (gapPrefix Q (k + 1)) ps = true := by
        simpa only [gapPrefix_succ] using h.2
      have hb := ih (k + 1) ht r (by simpa using hr)
      simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 r] using hb

private theorem checkGapLinks_sound (as bs ws : List ℕ)
    (h : checkGapLinks as bs ws = true) :
    ∀ r, r + 1 < ws.length →
      ws.getD (r + 1) 0 + as.getD r 0 = ws.getD r 0 + bs.getD r 0 := by
  induction ws generalizing as bs with
  | nil => simp
  | cons w ws ih =>
    cases ws with
    | nil => simp
    | cons v ws =>
      cases as with
      | nil => simp [checkGapLinks] at h
      | cons a as =>
        cases bs with
        | nil => simp [checkGapLinks] at h
        | cons b bs =>
          simp only [checkGapLinks, Bool.and_eq_true, decide_eq_true_eq] at h
          intro r hr
          cases r with
          | zero => simpa only [List.getD_cons_zero, List.getD_cons_succ] using h.1
          | succ r =>
            have hb := ih as bs h.2 r (by simpa using hr)
            simpa only [List.getD_cons_succ] using hb

private theorem getD_reverse (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs.reverse.getD i 0 = xs.getD (xs.length - 1 - i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

private theorem getD_tail (xs : List ℕ) (i : ℕ) :
    xs.tail.getD i 0 = xs.getD (i + 1) 0 := by
  cases xs <;> simp

/-- The linear list checks recover the exact closed-form gap weights. -/
private theorem checkGapWeights_sound (Q t : ℕ) (ps ws : List ℕ)
    (h : checkGapWeights Q t ps ws = true) :
    ws.length = t - 1 ∧ ∀ r < t - 1, ws.getD r 0 = gapWeight Q t r := by
  simp only [checkGapWeights, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp, hw⟩, hpre⟩, hfirst⟩, hlinks⟩ := h
  have hp0 : gapPrefix Q 0 = 0 := by simp [gapPrefix]
  have hpre' : checkGapPrefixes Q 0 (gapPrefix Q 0) ps = true := by
    simpa only [hp0] using hpre
  have hvalues := checkGapPrefixes_sound Q 0 ps hpre'
  refine ⟨hw, ?_⟩
  intro r hr
  induction r with
  | zero =>
    have ht : 1 < t := by omega
    have hpv := hvalues (t - 1) (by omega)
    have hrev := getD_reverse ps 0 (by omega)
    rw [hp] at hrev
    simp only [Nat.sub_zero] at hrev
    have hh : ws.getD 0 0 = ps.reverse.getD 0 0 := by
      simpa only [List.headD_eq_getD] using hfirst
    rw [hh, hrev, hpv, Nat.zero_add, gapWeight_zero Q t]
  | succ r ih =>
    have hir : r < t - 1 := by omega
    have hi := ih hir
    have hrec := checkGapLinks_sound ps.tail ps.reverse.tail ws hlinks r (by omega)
    rw [getD_tail, getD_tail, getD_reverse ps (r + 1) (by omega)] at hrec
    rw [hp, hvalues (r + 1) (by omega), hvalues (t - 1 - (r + 1)) (by omega)] at hrec
    simp only [Nat.zero_add] at hrec
    have hb := gapWeight_succ_balance Q t r (by omega)
    rw [hi] at hrec
    have he : t - 1 - (r + 1) = t - r - 2 := by omega
    rw [he] at hrec
    omega

/-- Linear prefix generator; a concrete result is validated by `checkGapWeights`. -/
def computeGapPrefixes (Q t : ℕ) : List ℕ :=
  (List.range (t - 1)).scanl (fun s k => s + ceilDiv Q ((k + 1) ^ 2)) 0

private def computeGapWeightsAux : ℕ → List ℕ → List ℕ → List ℕ
  | w, a :: as, b :: bs => w :: computeGapWeightsAux (w - a + b) as bs
  | w, _, _ => [w]

/-- Generate all weights by equation (25), with one forward and one backward prefix stream. -/
def computeGapWeights (Q t : ℕ) : List ℕ :=
  if t ≤ 1 then [] else
    let ps := computeGapPrefixes Q t
    computeGapWeightsAux (ps.getLastD 0) (ps.tail.take (t - 2))
      (ps.reverse.tail.take (t - 2))

/-- Weighted reciprocal adjacent gaps; both input lists are consumed sequentially. -/
def gapUpper : List ℕ → List ℕ → ℕ
  | w :: ws, x :: y :: ys => ceilDiv w (y - x) + gapUpper ws (y :: ys)
  | _, _ => 0

private theorem gapUpper_eq_sum (ws ds : List ℕ) (hlen : ws.length = ds.length - 1) :
    gapUpper ws ds = ∑ r ∈ range (ds.length - 1),
      ceilDiv (ws.getD r 0) (ds.getD (r + 1) 0 - ds.getD r 0) := by
  induction ds generalizing ws with
  | nil => simp [gapUpper]
  | cons x xs ih =>
    cases xs with
    | nil => simp [gapUpper]
    | cons y ys =>
      cases ws with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons w ws =>
        have hlen' : ws.length = (y :: ys).length - 1 := by
          simp only [List.length_cons] at *
          omega
        rw [gapUpper, ih ws hlen']
        simp only [List.length_cons, Nat.add_one_sub_one, sum_range_succ',
          List.getD_cons_zero, List.getD_cons_succ]
        omega

/-- A successful linear weight check identifies the sequential sum with equation (24). -/
private theorem gapUpper_eq_gapIndexUpper (Q : ℕ) (ps ws ds : List ℕ)
    (h : checkGapWeights Q ds.length ps ws = true) :
    gapUpper ws ds = gapIndexUpper Q ds.length (fun i => ds.getD i 0) := by
  obtain ⟨hlen, hvalues⟩ := checkGapWeights_sound Q ds.length ps ws h
  rw [gapUpper_eq_sum ws ds hlen]
  unfold gapIndexUpper
  apply sum_congr rfl
  intro r hr
  rw [hvalues r (mem_range.mp hr)]

private theorem image_getD (ds : List ℕ) :
    (range ds.length).image (fun i => ds.getD i 0) = ds.toFinset := by
  ext x
  simp only [mem_image, mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [← List.getElem_eq_getD 0 (h := hi)]
    exact List.getElem_mem hi
  · intro hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i, hi, by simpa only [List.getElem_eq_getD 0] using he⟩

/-- The linear checker bounds the complete reciprocal divisor sum. -/
theorem gapUpper_sound {n Q : ℕ} {ps ws ds : List ℕ}
    (h : checkGapWeights Q ds.length ps ws = true)
    (hs : ds.Pairwise (· < ·)) (he : ds.toFinset = n.divisors) :
    (Q : ℚ) * hHat n ≤ gapUpper ws ds := by
  have hd : ∀ i j, i < j → j < ds.length → ds.getD i 0 < ds.getD j 0 := by
    intro i j hij hj
    have hi : i < ds.length := lt_trans hij hj
    simpa only [List.getElem_eq_getD 0] using hs.rel_getElem_of_lt hi hj hij
  have he' : (range ds.length).image (fun i => ds.getD i 0) = n.divisors := by
    rw [image_getD, he]
  rw [gapUpper_eq_gapIndexUpper Q ps ws ds h]
  exact hHat_le_gapIndexUpper hd he'

#print axioms checkGapWeights_sound
#print axioms gapUpper_sound


end D5.S3.Arith.ErdosNicolas
