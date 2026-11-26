/- GID: D5/S3/Combinatorics/Graph/Chordal/WeightedSimplicialBanachPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/WeightedSimplicialBanachPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted simplicial and clique-tree averages bound gain reconstruction errors. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
import Mathlib.Analysis.Real.Sqrt

/-! # Weighted gain reconstruction on chordal graphs and clique trees -/

namespace SimpleGraph

open scoped BigOperators

namespace WeightedReconstruction

variable {V I E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private theorem skew_diag (g : V → V → E) (hs : ∀ x y, g y x = -g x y) (x : V) :
    g x x = 0 := by
  have h : (2 : ℝ) • g x x = 0 := by
    rw [two_smul, ← sub_neg_eq_add, ← hs x x, sub_self]
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

private theorem reverse_residual (g : V → V → E) (p : V → E)
    (hs : ∀ x y, g y x = -g x y) (x y : V) :
    g y x - (p x - p y) = -(g x y - (p y - p x)) := by rw [hs]; abel

private theorem weighted_norm {A : Finset V} {w : V → ℝ} {f : V → E} {B : ℝ}
    (hw : ∀ x ∈ A, 0 ≤ w x) (hf : ∀ x ∈ A, ‖f x‖ ≤ B) :
    ‖∑ x ∈ A, w x • f x‖ ≤ (∑ x ∈ A, w x) * B := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun x hx => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw x hx)]
    exact mul_le_mul_of_nonneg_left (hf x hx) (hw x hx)

private theorem center_sum {A : Finset V} {w : V → ℝ} (hw : ∑ x ∈ A, w x = 1)
    (p : V → E) (e : E) :
    ∑ x ∈ A, w x • (p x - e) = (∑ x ∈ A, w x • p x) - e := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]

private theorem predecessor_order [DecidableEq V] {G : SimpleGraph V} (hG : G.IsChordal)
    (A : Finset V) :
    ∃ r : V → ℕ, Set.InjOn r (A : Set V) ∧ (∀ x ∈ A, r x < A.card) ∧
      ∀ x ∈ A, G.IsClique {y | y ∈ A ∧ r y < r x ∧ G.Adj y x} := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · let : Nonempty (A : Set V) := ⟨⟨hA.choose, hA.choose_spec⟩⟩
      obtain ⟨z, hz⟩ := (hG.induce (A : Set V)).exists_isSimplicial
      let a : V := z.val
      have ha : a ∈ A := z.property
      let B := A.erase a
      obtain ⟨r, hr, hrB, hcl⟩ := ih B (Finset.erase_ssubset ha)
      have hc : B.card + 1 = A.card := Finset.card_erase_add_one ha
      let q (x : V) := if x = a then B.card else r x
      have old {x : V} (hx : x ∈ A) (hn : x ≠ a) : x ∈ B :=
        Finset.mem_erase.mpr ⟨hn, hx⟩
      have before {x : V} (hx : x ∈ A) (hn : x ≠ a) : q x < q a := by
        simpa [q, hn] using hrB x (old hx hn)
      refine ⟨q, ?_, ?_, ?_⟩
      · intro x hx y hy he
        by_cases hxa : x = a
        · subst x
          by_contra h
          exact (before hy (Ne.symm h)).ne he.symm
        · by_cases hya : y = a
          · subst y
            exact ((before hx hxa).ne he).elim
          · exact hr (old hx hxa) (old hy hya) (by simpa [q, hxa, hya] using he)
      · intro x hx
        by_cases hh : x = a
        · simp [q, hh, ← hc]
        · simpa [q, hh, ← hc] using (hrB x (old hx hh)).trans (Nat.lt_succ_self _)
      · intro x hx y hy w hw hn
        by_cases hh : x = a
        · subst x
          exact hz (show (⟨y, hy.1⟩ : (A : Set V)) ∈ _ from hy.2.2.symm)
            (show (⟨w, hw.1⟩ : (A : Set V)) ∈ _ from hw.2.2.symm)
            (by simpa [Subtype.ext_iff] using hn)
        · have hy' : y ≠ a := fun e => (before hx hh).asymm (e ▸ hy.2.1)
          have hw' : w ≠ a := fun e => (before hx hh).asymm (e ▸ hw.2.1)
          exact hcl x (old hx hh) ⟨old hy.1 hy', by simpa [q, hh, hy'] using hy.2.1, hy.2.2⟩
            ⟨old hw.1 hw', by simpa [q, hh, hw'] using hw.2.1, hw.2.2⟩ hn
    · simp only [Finset.not_nonempty_iff_eq_empty] at hA
      subst A
      exact ⟨fun _ => 0, by simp [Set.InjOn], by simp, by simp⟩

private theorem radius_parameters (k : ℕ) (hk : 2 ≤ k) :
    let R : ℝ := max ((k : ℝ) - 2) (((k : ℝ) - 1 + Real.sqrt (((k : ℝ) + 3)^2 - 16)) / 4)
    let s : ℝ := 1 / (1 + R)
    let t : ℝ := 1 - ((k : ℝ) - 1) * s
    1 ≤ R ∧ (k : ℝ) - 2 ≤ R ∧ 0 ≤ t ∧ t ≤ s ∧
      (1 - s) * (1 + R) = R ∧ ((k : ℝ) - 1) * s + (2*s - t)*R ≤ R := by
  dsimp only
  let a : ℝ := k
  let b := Real.sqrt ((a + 3)^2 - 16)
  let q := (a - 1 + b) / 4
  let R := max (a - 2) q
  change 1 ≤ R ∧ a - 2 ≤ R ∧ 0 ≤ 1 - (a - 1) * (1 / (1 + R)) ∧ _
  have ha : 2 ≤ a := by exact_mod_cast hk
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b^2 = (a + 3)^2 - 16 := Real.sq_sqrt (by nlinarith)
  have hb3 : 3 ≤ b := by nlinarith [sq_nonneg (a - 2)]
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hroot : 2*q^2 - (a - 1)*q - (a - 1) = 0 := by dsimp [q]; nlinarith
  have hbmax : b ≤ 3*(a - 1) := by
    by_contra! h
    have hc : (3*(a - 1))^2 < b^2 := by nlinarith [mul_pos (show 0 < b - 3*(a-1) by linarith)
      (show 0 < b + 3*(a-1) by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ a - 2 by linarith)]
  have hRmax : R ≤ a - 1 := max_le (by linarith) (by dsimp [q]; linarith)
  have hRq : q ≤ R := le_max_right _ _
  have hR : 1 ≤ R := hq.trans hRq
  have hRk : a - 2 ≤ R := le_max_left _ _
  have hn : 0 < 1 + R := by linarith
  have hpoly : 0 ≤ 2*R^2 - (a - 1)*R - (a - 1) := by
    have hp : 0 ≤ 2*(R+q) - (a - 1) := by dsimp [q] at *; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hRq) hp]
  refine ⟨hR, hRk, ?_, ?_, ?_, ?_⟩
  · apply sub_nonneg.mpr
    rw [mul_one_div, div_le_iff₀ hn]
    linarith
  · apply (sub_le_iff_le_add).2
    rw [← add_mul, mul_one_div, le_div_iff₀ hn]
    linarith
  · rw [sub_mul, one_mul, div_mul_cancel₀ _ hn.ne']; ring
  · rw [show (a - 1) * (1 / (1 + R)) + (2 * (1 / (1 + R)) -
        (1 - (a - 1) * (1 / (1 + R)))) * R =
        ((a - 1) + (a - R)*R) / (1 + R) by field_simp; ring]
    apply (div_le_iff₀ hn).2
    nlinarith

private noncomputable def predecessorWeight [DecidableEq V]
    (k : ℕ) (s t : ℝ) (A : Finset V) (a x : V) : ℝ :=
  if A.card = k then if x = a then t else s else 1 / (A.card : ℝ)

private theorem weight_total [DecidableEq V] {k : ℕ} {s t : ℝ} {A : Finset V}
    {a : V} (ha : a ∈ A) (ht : t = 1 - ((k : ℝ) - 1)*s) :
    (∑ x ∈ A, predecessorWeight k s t A a x) = 1 := by
  by_cases hc : A.card = k
  · rw [← A.sum_erase_add _ ha]
    have hcard : (((A.erase a).card : ℕ) : ℝ) + 1 = k := by
      exact_mod_cast (Finset.card_erase_add_one ha).trans hc
    have hs : ∑ x ∈ A.erase a, predecessorWeight k s t A a x =
        ((A.erase a).card : ℝ) * s := by
      rw [← Finset.sum_const, nsmul_eq_mul]
      exact Finset.sum_congr rfl fun x hx => by
        simp [predecessorWeight, hc, Finset.ne_of_mem_erase hx]
    rw [hs]
    simp only [predecessorWeight, hc, ite_true, ht]
    nlinarith
  · have hpos : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨a, ha⟩)
    simp [predecessorWeight, hc, nsmul_eq_mul, hpos]

private theorem erase_weighted_sum [DecidableEq V] {k : ℕ} {s t : ℝ} {A P : Finset V}
    (hAP : A ⊆ P) (hA : A.card + 1 = k) (hPk : P.card ≤ k)
    {b : V} (hb : b ∈ P) {f : V → E} {B : ℝ} (hB : 0 ≤ B)
    (hs : 0 ≤ s) (ht : t ≤ s) (hf : ∀ x ∈ P, ‖f x‖ ≤ B)
    (hz : ∑ x ∈ P, predecessorWeight k s t P b x • f x = 0) :
    ‖∑ x ∈ A, s • f x‖ ≤ (2*s-t)*B := by
  have hc := Finset.card_le_card hAP
  by_cases hP : P.card = k
  · obtain ⟨z, hzP, hzA⟩ := Finset.exists_mem_notMem_of_card_lt (s := A) (t := P) (by omega)
    have hEq : insert z A = P := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hzP hAP) (by rw [Finset.card_insert_of_notMem hzA]; omega)
    have hsum : ∑ x ∈ P, s • f x = (s-t) • f b := by
      rw [← P.sum_erase_add _ hb] at hz ⊢
      simp only [predecessorWeight, hP, ite_true] at hz
      have he : (∑ x ∈ P.erase b, (if x = b then t else s) • f x) =
          ∑ x ∈ P.erase b, s • f x :=
        Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]
      rw [he, add_eq_zero_iff_eq_neg] at hz
      rw [hz, sub_smul, neg_add_eq_sub]
    rw [← hEq, Finset.sum_insert hzA, add_comm] at hsum
    have he : (∑ x ∈ A, s • f x) = (s-t) • f b - s • f z := eq_sub_of_add_eq hsum
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht), abs_of_nonneg hs]
    calc
      _ ≤ (s-t)*B + s*B :=
        add_le_add (mul_le_mul_of_nonneg_left (hf b hb) (sub_nonneg.mpr ht))
          (mul_le_mul_of_nonneg_left (hf z hzP) hs)
      _ = _ := by ring
  · have he : A = P := Finset.eq_of_subset_of_card_le hAP (by omega)
    have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨b, hb⟩)
    simp only [predecessorWeight, hP, ite_false, ← Finset.smul_sum] at hz
    have hzero : ∑ x ∈ P, f x = 0 :=
      (smul_eq_zero.mp hz).resolve_left (by simp [hp])
    simp only [he, ← Finset.smul_sum, hzero, smul_zero, norm_zero]
    exact mul_nonneg (by linarith) hB

private theorem ordered_fit [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : V → ℕ} (hr : Function.Injective r)
    (P : V → Finset V) (hP : ∀ x y, x ∈ P y ↔ r x < r y ∧ G.Adj x y)
    (hcl : ∀ x, G.IsClique (P x : Set V)) {k : ℕ} (hk : ∀ x, (P x).card ≤ k)
    {R s t ε : ℝ} (hε : 0 ≤ ε) (hR : 1 ≤ R) (hk2 : 2 ≤ k) (hRk : (k : ℝ) - 2 ≤ R)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hts : t ≤ s) (ht' : t = 1 - ((k : ℝ)-1)*s)
    (hfixed : (1-s)*(1+R) = R) (hbudget : ((k : ℝ)-1)*s+(2*s-t)*R ≤ R)
    (g : V → V → E) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ p : V → E, ∀ x y, G.Adj x y → ‖g x y - (p y - p x)‖ ≤ R*ε := by
  classical
  let newest (x : V) : V := if h : (P x).Nonempty then
    (Finset.exists_max_image (P x) r h).choose else x
  have hn (x : V) (h : (P x).Nonempty) :
      newest x ∈ P x ∧ ∀ y ∈ P x, r y ≤ r (newest x) := by
    simpa [newest, h] using (Finset.exists_max_image (P x) r h).choose_spec
  let weight (x : V) := predecessorWeight k s t (P x) (newest x)
  have total (x : V) (hx : (P x).Nonempty) : ∑ y ∈ P x, weight x y = 1 :=
    weight_total (hn x hx).1 ht'
  have nonneg (x y : V) : 0 ≤ weight x y := by
    simp only [weight, predecessorWeight]
    split_ifs <;> positivity
  let res (p : V → E) (x y : V) : E := g x y - (p y - p x)
  have bound (n : ℕ) : ∃ p : V → E,
      (∀ x y, r x < n → r y < n → G.Adj x y → ‖res p x y‖ ≤ R*ε) ∧
      ∀ y, r y < n → ∑ x ∈ P y, weight y x • res p x y = 0 := by
    induction n with
    | zero => exact ⟨fun _ => 0, fun _ _ h => (Nat.not_lt_zero _ h).elim,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨p, hfit, hzero⟩ := ih
      by_cases hex : ∃ a, r a = n
      · obtain ⟨a, ha⟩ := hex
        let m : E := ∑ y ∈ P a, weight a y • (p y + g y a)
        let q (x : V) := if x = a then m else p x
        have hq {x : V} (hx : r x < n) : q x = p x := by
          have hne : x ≠ a := fun h => by subst x; omega
          simp [q, hne]
        have mem_rank {y x : V} (h : y ∈ P x) : r y < r x := ((hP y x).mp h).1
        have old {y : V} (hy : y ∈ P a) : r y < n := by simpa [ha] using mem_rank hy
        have res_new {x : V} (hx : x ∈ P a) : res q x a = p x + g x a - m := by
          simp only [res, q, ite_true]
          have hne : x ≠ a := ((hP x a).mp hx).2.ne
          simp only [hne, ite_false]
          abel
        have edge_new (x : V) (hx : x ∈ P a) : ‖res q x a‖ ≤ R*ε := by
          let A := (P a).erase x
          have hne : (P a).Nonempty := ⟨x, hx⟩
          let f (y : V) := g x a - (g x y + g y a)
          have rid (y : V) : p x + g x a - (p y + g y a) = res p x y + f y := by
            dsimp [res, f]; abel
          have hsum : res q x a = ∑ y ∈ A, weight a y • (res p x y + f y) := by
            rw [res_new hx, ← neg_sub (p x + g x a) m, ← center_sum (total a hne)]
            simp only [← Finset.sum_neg_distrib, ← smul_neg, neg_sub, rid]
            rw [← (P a).sum_erase_add _ hx]
            simp [res, f, skew_diag g hskew]
          have adj (y : V) (hy : y ∈ A) : G.Adj x y :=
            hcl a hx (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
          have hres (y : V) (hy : y ∈ A) : ‖res p x y‖ ≤ R*ε :=
            hfit x y (old hx) (old (Finset.mem_of_mem_erase hy)) (adj y hy)
          have hdef (y : V) (hy : y ∈ A) : ‖f y‖ ≤ ε := by
            rw [show f y = -(g x y + g y a - g x a) by dsimp [f]; abel, norm_neg]
            exact htri x y a (adj y hy) ((hP y a).mp (Finset.mem_of_mem_erase hy)).2
              ((hP x a).mp hx).2
          by_cases special : (P a).card = k ∧ x = newest a
          · obtain ⟨hcard, hxnew⟩ := special
            have hsub : A ⊆ P x := by
              intro y hy
              have hy' := Finset.mem_of_mem_erase hy
              apply (hP y x).2
              refine ⟨lt_of_le_of_ne (hxnew ▸ (hn a hne).2 y hy') ?_, (adj y hy).symm⟩
              exact fun h => Finset.ne_of_mem_erase hy (hr h)
            have hAc : A.card + 1 = k := (Finset.card_erase_add_one hx).trans hcard
            have hPn : (P x).Nonempty := Finset.card_pos.mp
              (by have := Finset.card_le_card hsub; have := hk a; omega)
            have hreverse : ∑ y ∈ P x, weight x y • res p x y = 0 := by
              calc
                _ = ∑ y ∈ P x, -(weight x y • res p y x) := by
                  exact Finset.sum_congr rfl fun y _ => by
                    simp only [res, reverse_residual g p hskew y x, smul_neg]
                _ = 0 := by rw [Finset.sum_neg_distrib, hzero x (old hx), neg_zero]
            have hold := erase_weighted_sum hsub hAc (hk x) (hn x hPn).1
              (mul_nonneg (by linarith) hε) hs hts
              (fun y hy => hfit x y (old hx) (by have := mem_rank hy; have := old hx; omega)
                ((hP y x).mp hy).2.symm) hreverse
            have hw (y : V) (hy : y ∈ A) : weight a y = s := by
              simp [weight, predecessorWeight, hcard, ← hxnew, Finset.ne_of_mem_erase hy]
            rw [hsum, Finset.sum_congr rfl (fun y hy => by rw [hw y hy]),
              show (∑ y ∈ A, s • (res p x y + f y)) =
                (∑ y ∈ A, s • res p x y) + ∑ y ∈ A, s • f y by
                  simp only [smul_add, Finset.sum_add_distrib]]
            have hdefsum := weighted_norm (A := A) (w := fun _ => s) (fun _ _ => hs) hdef
            have hAcR : (A.card : ℝ) + 1 = k := by exact_mod_cast hAc
            simp only [Finset.sum_const, nsmul_eq_mul] at hdefsum
            apply (norm_add_le _ _).trans
            calc
              _ ≤ (2*s-t)*(R*ε) + ((A.card : ℝ)*s)*ε := add_le_add hold hdefsum
              _ = (((k : ℝ)-1)*s+(2*s-t)*R)*ε := by
                rw [show (A.card : ℝ) = (k : ℝ)-1 by linarith]; ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hε
          · have hmass : ∑ y ∈ A, weight a y = 1 - weight a x := by
              have total_a := total a hne
              rw [← (P a).sum_erase_add _ hx] at total_a
              exact eq_sub_of_add_eq total_a
            have hw : (1-weight a x)*(1+R) ≤ R := by
              by_cases hc : (P a).card = k
              · have hxn : x ≠ newest a := fun e => special ⟨hc, e⟩
                simpa [weight, predecessorWeight, hc, hxn] using hfixed.le
              · have hp : 0 < ((P a).card : ℝ) := by exact_mod_cast hne.card_pos
                have hb : ((P a).card : ℝ) ≤ (k : ℝ)-1 := by
                  have hcard : (P a).card + 1 ≤ k := by have := hk a; omega
                  exact_mod_cast (show (P a).card ≤ k - 1 by omega)
                have hi : (1 : ℝ) ≤ (1/(P a).card)*(1+R) := by
                  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
                  linarith
                simp only [weight, predecessorWeight, hc, ite_false]
                nlinarith
            rw [hsum]
            refine (weighted_norm (nonneg a) (fun y hy => (norm_add_le _ _).trans ?_)).trans ?_
            · linarith [hres y hy, hdef y hy]
            · rw [hmass, show R*ε+ε = (1+R)*ε by ring, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right hw hε
        refine ⟨q, ?_, ?_⟩
        · intro x y hx hy hxy
          by_cases hya : y = a
          · subst y
            exact edge_new x ((hP x a).2 ⟨lt_of_le_of_ne (by omega) (fun e => hxy.ne (hr (e.trans ha.symm))), hxy⟩)
          · by_cases hxa : x = a
            · subst x
              rw [show res q a y = -res q y a from reverse_residual g q hskew y a, norm_neg]
              exact edge_new y ((hP y a).2 ⟨lt_of_le_of_ne (by omega)
                (fun e => hya (hr (e.trans ha.symm))), hxy.symm⟩)
            · have hx' : r x < n := by
                  have : r x ≠ n := fun e => hxa (hr (e.trans ha.symm))
                  omega
              have hy' : r y < n := by
                  have : r y ≠ n := fun e => hya (hr (e.trans ha.symm))
                  omega
              simpa only [res, hq hx', hq hy'] using hfit x y hx' hy' hxy
        · intro y hy
          by_cases e : y = a
          · subst y
            by_cases h : (P a).Nonempty
            · rw [Finset.sum_congr rfl (fun x hx => by rw [res_new hx]), center_sum (total a h)]
              exact sub_self m
            · simp [Finset.not_nonempty_iff_eq_empty.mp h]
          · have hy' : r y < n := by
              have : r y ≠ n := fun hh => e (hr (hh.trans ha.symm))
              omega
            rw [Finset.sum_congr rfl (fun x hx => by
              have hx' : r x < n := (mem_rank hx).trans hy'
              simp only [res, hq hx', hq hy'])]
            exact hzero y hy'
      · exact ⟨p, fun x y hx hy => hfit x y (by have := fun h => hex ⟨x, h⟩; omega)
          (by have := fun h => hex ⟨y, h⟩; omega),
          fun y hy => hzero y (by have := fun h => hex ⟨y, h⟩; omega)⟩
  obtain ⟨p, hp, -⟩ := bound ((Finset.univ : Finset V).sup r + 1)
  exact ⟨p, fun x y => hp x y (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ x)))
    (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ y)))⟩

end WeightedReconstruction

open WeightedReconstruction

/-- A reverse simplicial order permits a weighted average whose newest predecessor
uses the cancellation already established at its own insertion. -/
theorem IsChordal.exists_weighted_simplicial_banach_gain_potential
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 2 ≤ k)
    (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ k + 1)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤
      max ((k : ℝ) - 2) (((k : ℝ) - 1 + Real.sqrt (((k : ℝ) + 3)^2 - 16)) / 4) * ε := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨r, hr, -, hcl⟩ := predecessor_order hG (Finset.univ : Finset V)
  let P (x : V) : Finset V := Finset.univ.filter fun y => r y < r x ∧ G.Adj y x
  have hP (x y : V) : x ∈ P y ↔ r x < r y ∧ G.Adj x y := by simp [P]
  have hcl' (x : V) : G.IsClique (P x : Set V) := by
    simpa [P] using hcl x (Finset.mem_univ x)
  have hbound (x : V) : (P x).card ≤ k := by
    have hcl'' : G.IsClique (insert x (P x : Set V)) := by
      intro u hu v hv huv
      rcases hu with rfl | hu
      · exact ((hP _ _).mp (hv.resolve_left huv.symm)).2.symm
      · rcases hv with rfl | hv
        · exact ((hP _ _).mp hu).2
        · exact hcl' x hu hv huv
    have h := hclique _ hcl''
    rw [Set.ncard_insert_of_notMem (show x ∉ (P x : Set V) from fun hx =>
      (lt_irrefl _ ((hP _ _).mp hx).1)), Set.ncard_coe_finset] at h
    omega
  let R := max ((k : ℝ) - 2) (((k : ℝ) - 1 + Real.sqrt (((k : ℝ) + 3)^2 - 16)) / 4)
  let s : ℝ := 1 / (1 + R)
  let t := 1 - ((k : ℝ)-1)*s
  obtain ⟨hR, hRk, ht, hts, hfix, hbudget⟩ : 1 ≤ R ∧ (k : ℝ)-2 ≤ R ∧
      0 ≤ t ∧ t ≤ s ∧ (1-s)*(1+R) = R ∧ ((k : ℝ)-1)*s+(2*s-t)*R ≤ R :=
    radius_parameters k hk
  exact ordered_fit (fun {_ _} => hr (Finset.mem_univ _) (Finset.mem_univ _))
    P hP hcl' hbound hε hR hk hRk (ht.trans hts) ht hts rfl hfix hbudget g hskew htri


namespace WeightedReconstruction

variable {V I E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

private theorem distance_path (hT : T.IsTree) {a b : I} {p : T.Walk a b} (hp : p.IsPath) :
    T.dist a b = p.length := by
  obtain ⟨q, hq, hl⟩ := hT.connected.exists_path_of_dist a b
  have he : q = p := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path a b).elim ⟨q, hq⟩ ⟨p, hp⟩)
  exact hl.symm.trans (congrArg Walk.length he)

-- Paths leaving a root in different directions meet only at the root.
private theorem distance_across_branches (hT : T.IsTree) {a b x y : I}
    (hab : T.Adj a b) {p : T.Walk a x} {q : T.Walk a y}
    (hp : p.IsPath) (hq : q.IsPath) (hbp : b ∈ p.support) (hbq : b ∉ q.support) :
    T.dist x y = T.dist a x + T.dist a y := by
  classical
  have hd : p.reverse.support.Disjoint q.support.tail := by
    intro z hz hzq
    have hz₁ : z ∈ p.support := by simpa using hz
    have hz₂ := List.mem_of_mem_tail hzq
    have hza : z ≠ a := by
      intro h
      subst z
      have hn := hq.support_nodup
      rw [← List.cons_head_tail q.support_ne_nil] at hn
      exact (List.nodup_cons.mp hn).1 (by simpa using hzq)
    have he : p.takeUntil z hz₁ = q.takeUntil z hz₂ := congrArg Subtype.val
      ((hT.isAcyclic.subsingleton_path a z).elim ⟨_, hp.takeUntil hz₁⟩ ⟨_, hq.takeUntil hz₂⟩)
    have hfirst := hT.isAcyclic.eq_snd_of_adj_start hp hab hbp
    have hb : b ∈ (p.takeUntil z hz₁).support := by
      rw [hfirst, ← p.snd_takeUntil hza hz₁]
      exact List.mem_of_mem_tail (Walk.snd_mem_tail_support (Walk.not_nil_of_ne hza.symm))
    rw [he] at hb
    exact hbq (q.support_takeUntil_subset_support hz₂ hb)
  have happ := (p.reverse.isPath_append q).2 ⟨hp.reverse, hq.tail, hd⟩
  rw [distance_path hT happ, Walk.length_append, Walk.length_reverse,
    distance_path hT hp, distance_path hT hq]

private theorem occurrence_center [Finite I] (hK : IsCliqueTree T G K)
    (x : V) (D : ℕ) (hD : ∀ a b, x ∈ K a → x ∈ K b → T.dist a b ≤ D) :
    ∃ c, x ∈ K c ∧ ∀ a, x ∈ K a → T.dist c a ≤ (D+1)/2 := by
  classical
  let A := ({a : I | x ∈ K a} : Set I).toFinite.toFinset
  have memA (a : I) : a ∈ A ↔ x ∈ K a := by simp [A]
  obtain ⟨i, hi⟩ := hK.cover x
  have hA : A.Nonempty := ⟨i, (memA i).2 hi⟩
  let e (a : I) := A.sup (T.dist a)
  have he (a j : I) (hj : j ∈ A) : T.dist a j ≤ e a := Finset.le_sup (f := T.dist a) hj
  obtain ⟨a, ha, hmin⟩ := A.exists_min_image e hA
  refine ⟨a, (memA a).1 ha, fun j hj => (he a j ((memA j).2 hj)).trans ?_⟩
  by_contra! hlarge
  obtain ⟨x₀, hx₀, hxmax⟩ := A.exists_max_image (T.dist a) hA
  have hxlen : T.dist a x₀ = e a := (he a x₀ hx₀).antisymm (Finset.sup_le fun _ h => hxmax _ h)
  have hne : a ≠ x₀ := by
    intro h
    rw [← h, dist_self] at hxlen
    omega
  obtain ⟨p, hp, hpLen⟩ := hK.isTree.connected.exists_path_of_dist a x₀
  let b := p.snd
  have hpn := Walk.not_nil_of_ne hne (p := p)
  have hab : T.Adj a b := p.adj_snd hpn
  have hbp : b ∈ p.support := List.mem_of_mem_tail (p.snd_mem_tail_support hpn)
  have hb : b ∈ A := (memA b).2 (hK.running p hp x ((memA a).1 ha) ((memA x₀).1 hx₀) b hbp)
  have hbetter : e b ≤ e a - 1 := Finset.sup_le fun y hy => by
    obtain ⟨q, hq, hqLen⟩ := hK.isTree.connected.exists_path_of_dist a y
    by_cases hbq : b ∈ q.support
    · have hprefix : q.takeUntil b hbq = (Walk.nil : T.Walk b b).cons hab :=
        congrArg Subtype.val ((hK.isTree.isAcyclic.subsingleton_path a b).elim
          ⟨_, hq.takeUntil hbq⟩ (Path.singleton hab))
      have hlength := congrArg Walk.length (q.take_spec hbq)
      rw [Walk.length_append, hprefix, ← distance_path hK.isTree (hq.dropUntil hbq), hqLen] at hlength
      simp only [Walk.length] at hlength
      have := he a y hy
      omega
    · have hdist := distance_across_branches hK.isTree hab hp hq hbp hbq
      have hsum := hD x₀ y ((memA _).1 hx₀) ((memA _).1 hy)
      have htri := hK.isTree.connected.dist_triangle b a y
      rw [dist_eq_one_iff_adj.mpr hab.symm] at htri
      omega
  have := hmin b hb
  omega

private theorem fit_from_shift (g : V → V → E) (p q : V → E) (x y : V)
    {α B ε : ℝ} (hfit : ‖g x y - (p y - p x)‖ ≤ α*ε)
    (hx : ‖q x - p x‖ ≤ B*ε) (hy : ‖q y - p y‖ ≤ B*ε) :
    ‖g x y - (q y - q x)‖ ≤ (α + 2*B)*ε := by
  rw [show g x y - (q y - q x) =
      (g x y - (p y - p x)) + ((q x - p x) - (q y - p y)) by abel]
  exact (norm_add_le _ _).trans (by linarith [norm_sub_le (q x - p x) (q y - p y)])

private theorem along_occurrences (hK : IsCliqueTree T G K) (p : I → V → E)
    (B : ℝ) (hB : ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, ‖p b x - p a x‖ ≤ B)
    (x : V) {a b : I} (ha : x ∈ K a) (hb : x ∈ K b) :
    ‖p b x - p a x‖ ≤ (T.dist a b : ℝ)*B := by
  have along {i j : I} (q : T.Walk i j) (h : ∀ c ∈ q.support, x ∈ K c) :
      ‖p j x - p i x‖ ≤ (q.length : ℝ)*B := by
    induction q with
    | nil => simp
    | @cons i k j hik q ih =>
      have hstep := hB i k hik x ⟨h _ (by simp), h _ (by simp)⟩
      have hend := ih fun c hc => h c (by simp [hc])
      rw [show p j x - p i x = (p j x - p k x) + (p k x - p i x) by abel]
      exact (norm_add_le _ _).trans (by push_cast [Walk.length]; linarith)
  obtain ⟨q, hq, hl⟩ := hK.isTree.connected.exists_path_of_dist a b
  simpa [hl] using along q (hK.running q hq x ha hb)

open Classical in
private noncomputable def separator (K : I → Set V) (a b : I) [Finite V] : Finset V :=
  (K a ∩ K b).toFinite.toFinset

private theorem mem_separator [Finite V] {a b : I} {x : V} :
    x ∈ separator K a b ↔ x ∈ K a ∩ K b := by simp [separator]

private theorem sep_card [Finite V] (a b : I) :
    (separator K a b).card = (K a ∩ K b).ncard :=
  (Set.ncard_eq_toFinset_card _ (K a ∩ K b).toFinite).symm

private theorem weighted_bags [Fintype V] (hK : IsCliqueTree T G K)
    (π : I → V → ℝ) (hπ : ∀ a x, 0 ≤ π a x) (hsupp : ∀ a x, x ∉ K a → π a x = 0)
    (htotal : ∀ a, ∑ x, π a x = 1) {α d ε : ℝ} (hε : 0 ≤ ε)
    (hα : ∀ a u v, u ∈ K a → v ∈ K a → G.Adj u v → 1 - π a u - π a v ≤ α)
    (hd : ∀ a b, T.Adj a b →
      (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
        (1 - ∑ x ∈ (K a ∩ K b).toFinite.toFinset, min (π a x) (π b x)) ≤ d)
    (g : V → V → E) (hskew : ∀ u v, g v u = -g u v)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖g u v + g v w - g u w‖ ≤ ε) :
    ∃ ψ : I → V → E,
      (∀ a u v, u ∈ K a → v ∈ K a → G.Adj u v → ‖g u v - (ψ a v - ψ a u)‖ ≤ α*ε) ∧
      ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, ‖ψ b x - ψ a x‖ ≤ 2*d*ε := by
  classical
  let p (a : I) (x : V) := ∑ z, π a z • g z x
  let F (u v z : V) : E := g u v - (g z v - g z u)
  have hz₁ (u v : V) : F u v u = 0 := by simp [F, skew_diag g hskew]
  have hz₂ (u v : V) : F u v v = 0 := by simp [F, skew_diag g hskew, hskew u v]
  have def_bound (a : I) (u v z : V) (hu : u ∈ K a) (hv : v ∈ K a) (hz : z ∈ K a) :
      ‖F u v z‖ ≤ ε := by
    by_cases h : u = v
    · subst v
      simpa [F, skew_diag g hskew] using hε
    by_cases hzu : z = u
    · simpa [hzu, hz₁] using hε
    by_cases hzv : z = v
    · simpa [hzv, hz₂] using hε
    rw [show F u v z = g z u + g u v - g z v by dsimp [F]; abel]
    exact htri z u v (hK.clique a hz hu hzu) (hK.clique a hu hv h) (hK.clique a hz hv hzv)
  have res (a : I) (u v : V) : g u v - (p a v - p a u) = ∑ z, π a z • F u v z := by
    simp only [F, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, htotal, one_smul, p]
    rw [Finset.sum_sub_distrib]
  let gain (a b : I) : E :=
    ((separator K a b).card : ℝ)⁻¹ • ∑ x ∈ separator K a b, (p a x - p b x)
  have hrev (a b : I) : gain b a = -gain a b := by
    simp only [gain, separator, Set.inter_comm (K b) (K a)]
    simp only [Finset.sum_sub_distrib, smul_sub, neg_sub]
  obtain ⟨c, hc⟩ := tree_offsets hK.isTree gain (fun a b _ => hrev a b)
  let ψ (a : I) (x : V) := p a x + c a
  refine ⟨ψ, ?_, ?_⟩
  · intro a u v hu hv huv
    let A := ((Finset.univ : Finset V).erase u).erase v
    have hvA : v ∈ (Finset.univ : Finset V).erase u :=
      Finset.mem_erase.mpr ⟨huv.ne.symm, Finset.mem_univ _⟩
    have hmass : ∑ z ∈ A, π a z = 1 - π a u - π a v := by
      have h := htotal a
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u), ← Finset.sum_erase_add _ _ hvA] at h
      dsimp [A]; linarith
    rw [show ψ a v - ψ a u = p a v - p a u by dsimp [ψ]; abel, res,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ u), ← Finset.sum_erase_add _ _ hvA]
    simp only [hz₁, hz₂, smul_zero, add_zero]
    -- A weight of zero makes a summand vanish even outside its bag.
    apply le_trans (b := (∑ z ∈ A, π a z)*ε)
    · apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro z hz
      by_cases hza : z ∈ K a
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hπ a z)]
        exact mul_le_mul_of_nonneg_left (def_bound a u v z hu hv hza) (hπ a z)
      · simp [hsupp a z hza]
    · rw [hmass]
      exact mul_le_mul_of_nonneg_right (hα a u v hu hv huv) hε
  · intro a b hab u hu
    let S := separator K a b
    have huS : u ∈ S := mem_separator.mpr hu
    let m (z : V) := if z ∈ S then min (π a z) (π b z) else 0
    let M : ℝ := 1 - ∑ z ∈ S, min (π a z) (π b z)
    have hm : ∑ z, m z = ∑ z ∈ S, min (π a z) (π b z) := by
      simp [m, Finset.sum_filter]
    have inc (v : V) (hvS : v ∈ S) :
        ‖(p b u - p a u) - (p b v - p a v)‖ ≤ 2*M*ε := by
      have hv : v ∈ K a ∩ K b := mem_separator.mp hvS
      have cancel (j : I) (hu' : u ∈ K j) (hv' : v ∈ K j)
          (hs : ∀ z ∈ S, z ∈ K j) (hmin : ∀ z ∈ S, m z ≤ π j z) :
          ‖(∑ z, π j z • F u v z) - ∑ z, m z • F u v z‖ ≤ M*ε := by
        rw [← Finset.sum_sub_distrib]
        simp only [← sub_smul]
        have hmass : ∑ z, (π j z - m z) = M := by simp [Finset.sum_sub_distrib, htotal, hm, M]
        apply le_trans (b := (∑ z, (π j z - m z))*ε)
        · apply (norm_sum_le _ _).trans
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro z _
          by_cases hz : z ∈ K j
          · have hw : 0 ≤ π j z - m z := sub_nonneg.mpr (by
              by_cases hzS : z ∈ S
              · exact hmin z hzS
              · simpa [m, hzS] using hπ j z)
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
            exact mul_le_mul_of_nonneg_left (def_bound j u v z hu' hv' hz) hw
          · have hzS : z ∉ S := fun h => hz (hs z h)
            simp [hsupp j z hz, m, hzS]
        · rw [hmass]
      have h₁ := cancel a hu.1 hv.1 (fun z hz => (mem_separator.mp hz).1)
        (fun z hz => by simp [m, hz, min_le_left])
      have h₂ := cancel b hu.2 hv.2 (fun z hz => (mem_separator.mp hz).2)
        (fun z hz => by simp [m, hz, min_le_right])
      rw [show (p b u - p a u) - (p b v - p a v) =
          ((∑ z, π b z • F u v z) - ∑ z, m z • F u v z) -
          ((∑ z, π a z • F u v z) - ∑ z, m z • F u v z) by rw [← res, ← res]; abel]
      exact (norm_sub_le _ _).trans (by linarith)
    let f (v : V) := (p b u - p a u) - (p b v - p a v)
    have hSc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨u, huS⟩
    have hshift : ψ b u - ψ a u = (S.card : ℝ)⁻¹ • ∑ v ∈ S.erase u, f v := by
      have hfull : (S.card : ℝ)⁻¹ • (∑ v ∈ S, f v) =
          p b u - p a u + gain a b := by
        simp only [f, Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
          smul_sub, smul_smul, inv_mul_cancel₀ hSc.ne', one_smul, gain, S]
        abel
      have he : ∑ v ∈ S, f v = ∑ v ∈ S.erase u, f v := by
        rw [← S.sum_erase_add _ huS]
        simp [f]
      rw [← he, hfull, ← hc a b hab]
      dsimp [ψ]; abel
    rw [hshift, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hSc.le)]
    have hsum : ‖∑ v ∈ S.erase u, f v‖ ≤ ((S.erase u).card : ℝ)*(2*M*ε) := by
      apply (norm_sum_le _ _).trans
      exact (Finset.sum_le_sum fun v hv => inc v (Finset.mem_of_mem_erase hv)).trans_eq (by simp [nsmul_eq_mul])
    have hcard : ((S.erase u).card : ℝ) + 1 = S.card := by exact_mod_cast Finset.card_erase_add_one huS
    calc
      _ ≤ (S.card : ℝ)⁻¹ * (((S.erase u).card : ℝ)*(2*M*ε)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hSc.le)
      _ = 2 * ((1 - 1/(S.card : ℝ))*M) * ε := by
        rw [show ((S.erase u).card : ℝ) = S.card - 1 by linarith]
        field_simp
        <;> ring
      _ ≤ 2*d*ε := by
        have hz : (1 - 1/(S.card : ℝ))*M ≤ d := by simpa [S, M, sep_card, separator] using hd a b hab
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) hε

private theorem midpoint_occurrences [Finite I] (hK : IsCliqueTree T G K)
    (ψ : I → V → E) {B : ℝ} (hB : 0 ≤ B)
    (hshift : ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, ‖ψ b x - ψ a x‖ ≤ 2*B)
    {D : ℕ} (hsmall : D ≤ 1)
    (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ D) :
    ∃ φ : V → E, ∀ a x, x ∈ K a →
      ‖φ x - ψ a x‖ ≤ B ∧ (D = 0 → φ x = ψ a x) := by
  classical
  have adjacent (x : V) {a b : I} (ha : x ∈ K a) (hb : x ∈ K b) (hne : a ≠ b) :
      T.Adj a b := by
    apply dist_eq_one_iff_adj.mp
    have hz := (hK.isTree.connected a b).pos_dist_of_ne hne
    have h := hD x a b ha hb
    omega
  let a (x : V) := (hK.cover x).choose
  have ha (x : V) : x ∈ K (a x) := (hK.cover x).choose_spec
  let alt (x : V) := ∃ b, b ≠ a x ∧ x ∈ K b
  let φ (x : V) := if h : alt x then (1/2 : ℝ) • (ψ (a x) x + ψ h.choose x) else ψ (a x) x
  refine ⟨φ, fun c x hx => ?_⟩
  by_cases h : alt x
  · obtain ⟨hne, hb⟩ := h.choose_spec
    have hab := adjacent x (ha x) hb hne.symm
    have hcb : c = a x ∨ c = h.choose := by
      by_cases hca : c = a x
      · exact Or.inl hca
      · right
        by_contra hne'
        have hca' := adjacent x hx (ha x) hca
        have hcb' := adjacent x hx hb hne'
        exact hK.isTree.dist_ne_of_adj c hab
          ((dist_eq_one_iff_adj.mpr hca').trans (dist_eq_one_iff_adj.mpr hcb').symm)
    have he : D ≠ 0 := by
      have := hD x _ _ (ha x) hb
      rw [dist_eq_one_iff_adj.mpr hab] at this
      omega
    refine ⟨?_, fun hD0 => (he hD0).elim⟩
    have hmid (u v : E) (h : ‖v-u‖ ≤ 2*B) : ‖(1/2 : ℝ) • (u+v) - u‖ ≤ B := by
      rw [show (1/2 : ℝ) • (u+v) - u = (1/2 : ℝ) • (v-u) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      linarith
    rcases hcb with rfl | rfl
    · simpa [φ, h] using hmid _ _ (hshift _ _ hab x ⟨ha x, hb⟩)
    · simpa [φ, h, add_comm] using hmid _ _ (hshift _ _ hab.symm x ⟨hb, ha x⟩)
  · have he : c = a x := by by_contra hn; exact h ⟨c, hn, hx⟩
    simp [φ, h, he, hB]

end WeightedReconstruction

/-- Translating the weighted bag potentials limits variation on each separator.
The center of each occurrence subtree controls how far an edge endpoint moves.
At occurrence diameter at most one, its one or two occurrences admit a midpoint. -/
theorem cliqueTree_occurrenceCenter_banach_potential
    {V : Type*} [Fintype V] {I : Type*} [Finite I]
    {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (hK : IsCliqueTree T G K)
    (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (π : I → V → ℝ) (hπ : ∀ a x, 0 ≤ π a x)
    (hsupp : ∀ a x, x ∉ K a → π a x = 0) (htotal : ∀ a, ∑ x, π a x = 1)
    (α d : ℝ) (hα₀ : 0 ≤ α) (hd₀ : 0 ≤ d)
    (hα : ∀ a u v, u ∈ K a → v ∈ K a → G.Adj u v → 1 - π a u - π a v ≤ α)
    (hd : ∀ a b, T.Adj a b →
      (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
        (1 - ∑ x ∈ (K a ∩ K b).toFinite.toFinset, min (π a x) (π b x)) ≤ d)
    (D : ℕ) (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ D)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ u v, g v u = -g u v)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖g u v + g v w - g u w‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (α + 4 * (((D+1)/2 : ℕ) : ℝ) * d) * ε ∧
      (D ≤ 1 → ‖g u v - (φ v - φ u)‖ ≤ (α + 2*d) * ε) := by
  classical
  obtain ⟨ψ, hfit, hshift⟩ := weighted_bags hK π hπ hsupp htotal hε hα hd g hskew htri
  by_cases hsmall : D ≤ 1
  · obtain ⟨φ, hclose⟩ := midpoint_occurrences hK ψ (mul_nonneg hd₀ hε)
      (fun a b h x hx => by simpa [mul_assoc] using hshift a b h x hx) hsmall hD
    refine ⟨φ, fun u v huv => ?_⟩
    obtain ⟨a, hu, hv⟩ := hK.edge u v huv
    have hmid := fit_from_shift g (ψ a) φ u v (hfit a u v hu hv huv)
      (hclose a u hu).1 (hclose a v hv).1
    refine ⟨?_, fun _ => hmid⟩
    by_cases hzero : D = 0
    · simpa [hzero, (hclose a u hu).2 hzero, (hclose a v hv).2 hzero] using hfit a u v hu hv huv
    · have he : (D+1)/2 = 1 := by omega
      rw [he]
      exact hmid.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) hε)
  · choose c hc hcenter using fun x => occurrence_center hK x D (hD x)
    let φ (x : V) := ψ (c x) x
    have close (a : I) (x : V) (hx : x ∈ K a) :
        ‖φ x - ψ a x‖ ≤ (2 * (((D+1)/2 : ℕ) : ℝ) * d) * ε := by
      have hdist : (T.dist (c x) a : ℝ) ≤ (((D+1)/2 : ℕ) : ℝ) := by
        exact_mod_cast hcenter x a hx
      rw [show φ x - ψ a x = -(ψ a x - ψ (c x) x) by dsimp [φ]; abel, norm_neg]
      exact (along_occurrences hK ψ (2*d*ε) hshift x (hc x) hx).trans
        (by convert mul_le_mul_of_nonneg_right hdist (mul_nonneg (by positivity : 0 ≤ 2*d) hε)
          using 1 <;> ring)
    refine ⟨φ, fun u v huv => ⟨?_, fun h => (hsmall h).elim⟩⟩
    obtain ⟨a, hu, hv⟩ := hK.edge u v huv
    convert fit_from_shift g (ψ a) φ u v (hfit a u v hu hv huv) (close a u hu) (close a v hv)
      using 1 <;> ring

end SimpleGraph
