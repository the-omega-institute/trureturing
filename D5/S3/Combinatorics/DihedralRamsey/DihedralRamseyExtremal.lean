/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyExtremal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyExtremal
   mirror-E: none(waiver:finite-zigzag-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Nearest-neighbor injections control the loss of zigzag ends. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyZigzag
import D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs
open CyclicRamseyDefs

theorem not_cyclic_of_not_dihedral {a n : ℕ} (G : SimpleGraph (Fin n))
    (h : ¬ DihedralEmbeddable (altPath a) G) :
    ¬ CyclicEmbeddable (altPath a) G := by
  intro hc
  rcases hc with ⟨s, ψ, hψ, hE⟩
  apply h
  exact ⟨s, false, ψ, hψ, hE⟩

set_option maxHeartbeats 1000000 in
-- The insertion proof checks every configuration of the cyclic cut.
/-- Insert the next alternating rank into the empty terminal arc. -/
theorem append_zigzag {k n : ℕ} (hk : 1 ≤ k) (G : SimpleGraph (Fin n))
    (f : altPath (k + 1) →g G)
    (hf : StrictMono fun i => ((f i) - (f 0)).val)
    (i j : Fin (k + 1)) (hi : i.val = altVertex (k + 1) (k - 1))
    (hj : j.val = altVertex (k + 1) k) (z : Fin n) (hz : G.Adj (f j) z)
    (harc : if k % 2 = 1 then ((f i) - (f j)).val < (z - (f j)).val
      else (z - (f j)).val < ((f i) - (f j)).val) :
    ∃ f' : altPath (k + 2) →g G,
      StrictMono (fun v => ((f' v) - (f' 0)).val) ∧
      ∃ p q : Fin (k + 2), p.val = altVertex (k + 2) k ∧
        q.val = altVertex (k + 2) (k + 1) ∧ f' p = f j ∧ f' q = z := by
  have hdist (x y : Fin n) : (y - x).val =
      if x.val ≤ y.val then y.val - x.val else n + y.val - x.val := by
    split_ifs with hxy
    · exact Fin.sub_val_of_le hxy
    · exact Fin.coe_sub_iff_lt.mpr (by omega)
  let t := (k + 2) / 2
  have ht : 1 ≤ t ∧ t ≤ k := by dsimp [t]; omega
  let lo : Fin (k + 1) := ⟨t - 1, by omega⟩
  let up : Fin (k + 1) := ⟨t, by omega⟩
  have horder := hf (show lo < up by simp only [Fin.lt_def, lo, up]; omega)
  have hgap : ((f lo) - (f 0)).val < (z - (f 0)).val ∧
      (z - (f 0)).val < ((f up) - (f 0)).val := by
    have hlo := (f lo).isLt
    have hup := (f up).isLt
    have hzero := (f 0).isLt
    have hzn := z.isLt
    have hzne := hz.ne
    by_cases hp : k % 2 = 1
    · have hil : i = lo := by
        apply Fin.ext
        dsimp [lo, t]
        dsimp [altVertex] at hi
        split_ifs at hi <;> omega
      have hju : j = up := by
        apply Fin.ext
        dsimp [up, t]
        dsimp [altVertex] at hj
        split_ifs at hj <;> omega
      rw [if_pos hp, hil, hju] at harc
      rw [hju] at hzne
      have hzval : (f up).val ≠ z.val := fun h => hzne (Fin.ext h)
      simp only [hdist] at horder harc ⊢
      split_ifs at horder harc ⊢ <;> omega
    · have hiu : i = up := by
        apply Fin.ext
        dsimp [up, t]
        dsimp [altVertex] at hi
        split_ifs at hi <;> omega
      have hjl : j = lo := by
        apply Fin.ext
        dsimp [lo, t]
        dsimp [altVertex] at hj
        split_ifs at hj <;> omega
      rw [if_neg hp, hiu, hjl] at harc
      rw [hjl] at hzne
      have hzval : (f lo).val ≠ z.val := fun h => hzne (Fin.ext h)
      simp only [hdist] at horder harc ⊢
      split_ifs at horder harc ⊢ <;> omega
  let g : Fin (k + 2) → Fin n := fun v =>
    if h : v.val < t then f ⟨v.val, by omega⟩
    else if v.val = t then z else f ⟨v.val - 1, by omega⟩
  have hg0 : g 0 = f 0 := by
    simp only [g, dif_pos (show (0 : Fin (k + 2)).val < t by change 0 < t; omega)]
    congr 1
  have hmono : StrictMono fun v => ((g v) - (g 0)).val := by
    intro u v huv
    rw [hg0]
    have hu := u.isLt
    have hv := v.isLt
    change u.val < v.val at huv
    dsimp [g]
    split_ifs with hut hut' hvt hvt'
    · apply hf
      exact huv
    · have hul : (⟨u.val, by omega⟩ : Fin (k + 1)) ≤ lo := by
        simp only [Fin.le_def, lo]
        omega
      exact (hf.monotone hul).trans_lt hgap.1
    · have hul : (⟨u.val, by omega⟩ : Fin (k + 1)) ≤ lo := by
        simp only [Fin.le_def, lo]
        omega
      have huv' : up ≤ (⟨v.val - 1, by omega⟩ : Fin (k + 1)) := by
        simp only [Fin.le_def, up]
        omega
      exact (hf.monotone hul).trans_lt (hgap.1.trans (hgap.2.trans_le (hf.monotone huv')))
    · omega
    · omega
    · have huv' : up ≤ (⟨v.val - 1, by omega⟩ : Fin (k + 1)) := by
        simp only [Fin.le_def, up]
        omega
      exact hgap.2.trans_le (hf.monotone huv')
    · omega
    · omega
    · apply hf
      change u.val - 1 < v.val - 1
      omega
  have hbound : ∀ l : ℕ, l < k + 1 → altVertex (k + 1) l < k + 1 := by
    intro l hl
    dsimp [altVertex]
    split_ifs <;> omega
  have hbound' : ∀ l : ℕ, l < k + 2 → altVertex (k + 2) l < k + 2 := by
    intro l hl
    dsimp [altVertex]
    split_ifs <;> omega
  have hkeep : ∀ l : ℕ, (hl : l < k + 1) →
      g ⟨altVertex (k + 2) l, hbound' l (by omega)⟩ =
        f ⟨altVertex (k + 1) l, hbound l hl⟩ := by
    intro l hl
    dsimp [g, altVertex, t]
    split_ifs <;> first | omega | (congr 1; apply Fin.ext; dsimp only; omega)
  have hlast : altVertex (k + 2) (k + 1) = t := by
    dsimp [altVertex, t]
    split_ifs <;> omega
  have hgj : g ⟨altVertex (k + 2) k, hbound' k (by omega)⟩ = f j := by
    rw [hkeep k (by omega)]
    congr 1
    exact Fin.ext hj.symm
  have hgz : g ⟨altVertex (k + 2) (k + 1), hbound' (k + 1) (by omega)⟩ = z := by
    simp [g, hlast]
  have hmap : ∀ u v, (altPath (k + 2)).Adj u v → G.Adj (g u) (g v) := by
    intro u v huv
    rw [altPath, SimpleGraph.fromRel_adj] at huv
    have hedges : ∀ (l : ℕ) (hl : l + 1 < k + 2),
        G.Adj (g ⟨altVertex (k + 2) l, hbound' l (by omega)⟩)
          (g ⟨altVertex (k + 2) (l + 1), hbound' (l + 1) (by omega)⟩) := by
      intro l hl
      by_cases hle : l < k
      · rw [hkeep l (by omega), hkeep (l + 1) (by omega)]
        apply f.map_adj
        rw [altPath, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨l, by omega, rfl, rfl⟩⟩
        intro he
        have he' := congrArg Fin.val he
        dsimp [altVertex] at he'
        split_ifs at he' <;> omega
      · have he : l = k := by omega
        subst l
        rw [hgj, hgz]
        exact hz
    rcases huv.2 with ⟨l, hl, hu, hv⟩ | ⟨l, hl, hv, hu⟩
    · have hu' : u = ⟨altVertex (k + 2) l, hbound' l (by omega)⟩ := Fin.ext hu
      have hv' : v = ⟨altVertex (k + 2) (l + 1), hbound' (l + 1) (by omega)⟩ :=
        Fin.ext hv
      rw [hu', hv']
      exact hedges l hl
    · have hu' : u = ⟨altVertex (k + 2) (l + 1), hbound' (l + 1) (by omega)⟩ :=
        Fin.ext hu
      have hv' : v = ⟨altVertex (k + 2) l, hbound' l (by omega)⟩ := Fin.ext hv
      rw [hu', hv']
      exact (hedges l hl).symm
  let f' : altPath (k + 2) →g G := ⟨g, fun {u v} h => hmap u v h⟩
  exact ⟨f', hmono, ⟨altVertex (k + 2) k, hbound' k (by omega)⟩,
    ⟨altVertex (k + 2) (k + 1), hbound' (k + 1) (by omega)⟩, rfl, rfl, hgj, hgz⟩


/-- End extension loses at most one ordered edge at each terminal vertex. -/
theorem end_extension_count {n : ℕ} (G : SimpleGraph (Fin n))
    (E E' : Finset (Fin n × Fin n)) (up : Bool)
    (hE : ∀ p ∈ E, G.Adj p.1 p.2)
    (hstep : ∀ p ∈ E, ∀ z, G.Adj p.2 z →
      (if up then (p.1 - p.2).val < (z - p.2).val
       else (z - p.2).val < (p.1 - p.2).val) → (p.2, z) ∈ E') :
    E.card ≤ E'.card + n := by
  classical
  have hdist (x y : Fin n) : (y - x).val =
      if x.val ≤ y.val then y.val - x.val else n + y.val - x.val := by
    split_ifs with hxy
    · exact Fin.sub_val_of_le hxy
    · exact Fin.coe_sub_iff_lt.mpr (by omega)
  have hd : ∀ y : Fin n, Function.Injective (fun x => (x - y).val) := by
    intro y x z hx
    apply Fin.ext
    have hxn := x.isLt
    have hzn := z.isLt
    simp only [hdist] at hx
    split_ifs at hx <;> omega
  let eligible (p : Fin n × Fin n) : Finset (Fin n) := Finset.univ.filter fun z =>
    G.Adj p.2 z ∧ (if up then (p.1 - p.2).val < (z - p.2).val
      else (z - p.2).val < (p.1 - p.2).val)
  have nearest : ∀ p, (eligible p).Nonempty →
      ∃ z ∈ eligible p, ∀ w ∈ eligible p,
        if up then (z - p.2).val ≤ (w - p.2).val
        else (w - p.2).val ≤ (z - p.2).val := by
    intro p hp
    cases up with
    | false =>
      obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (eligible p) (fun x => (x - p.2).val) hp
      exact ⟨z, hz, hmax⟩
    | true =>
      obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (eligible p) (fun x => (x - p.2).val) hp
      exact ⟨z, hz, hmin⟩
  let chosen (p : Fin n × Fin n) (hp : (eligible p).Nonempty) : Fin n :=
    Classical.choose (nearest p hp)
  have chosen_spec : ∀ p hp, chosen p hp ∈ eligible p ∧
      ∀ w ∈ eligible p, if up then ((chosen p hp) - p.2).val ≤ (w - p.2).val
      else (w - p.2).val ≤ ((chosen p hp) - p.2).val := by
    intro p hp
    exact Classical.choose_spec (nearest p hp)
  let F (p : E) : E' ⊕ Fin n :=
    if hp : (eligible p.val).Nonempty then
      Sum.inl ⟨(p.val.2, chosen p.val hp), hstep p.val p.property _
        (Finset.mem_filter.mp (chosen_spec p.val hp).1).2.1
        (Finset.mem_filter.mp (chosen_spec p.val hp).1).2.2⟩
    else Sum.inr p.val.2
  have hF : Function.Injective F := by
    intro p q hpq
    by_cases hp : (eligible p.val).Nonempty
    · by_cases hq : (eligible q.val).Nonempty
      · have he : (p.val.2, chosen p.val hp) = (q.val.2, chosen q.val hq) := by
          simpa only [F, dif_pos hp, dif_pos hq, Sum.inl.injEq, Subtype.mk.injEq] using hpq
        have hy : p.val.2 = q.val.2 := congrArg Prod.fst he
        have hz : chosen p.val hp = chosen q.val hq := congrArg Prod.snd he
        have hzp := (Finset.mem_filter.mp (chosen_spec p.val hp).1).2.2
        have hzq := (Finset.mem_filter.mp (chosen_spec q.val hq).1).2.2
        have hpx := (hE p.val p.property).symm
        have hqx := (hE q.val q.property).symm
        have hsame : (p.val.1 - p.val.2).val = (q.val.1 - q.val.2).val := by
          by_contra hn
          have hn' : (p.val.1 - p.val.2).val ≠ (q.val.1 - p.val.2).val := by
            simpa only [hy] using hn
          rcases lt_or_gt_of_ne hn' with hlt | hgt
          · cases up with
            | false =>
              have hex : p.val.1 ∈ eligible q.val := by
                simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by simpa only [hy] using hpx, by simpa [hy] using hlt⟩
              have hm := (chosen_spec q.val hq).2 _ hex
              simp only [Bool.false_eq_true, ↓reduceIte] at hm hzp hzq
              rw [← hy, ← hz] at hm hzq
              omega
            | true =>
              have hex : q.val.1 ∈ eligible p.val := by
                simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by simpa only [hy] using hqx, hlt⟩
              have hm := (chosen_spec p.val hp).2 _ hex
              simp only [↓reduceIte] at hm hzp hzq
              rw [← hy, ← hz] at hzq
              omega
          · cases up with
            | false =>
              have hex : q.val.1 ∈ eligible p.val := by
                simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by simpa only [hy] using hqx, hgt⟩
              have hm := (chosen_spec p.val hp).2 _ hex
              simp only [Bool.false_eq_true, ↓reduceIte] at hm hzp hzq
              rw [← hy, ← hz] at hzq
              omega
            | true =>
              have hex : p.val.1 ∈ eligible q.val := by
                simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by simpa only [hy] using hpx, by simpa [hy] using hgt⟩
              have hm := (chosen_spec q.val hq).2 _ hex
              simp only [↓reduceIte] at hm hzp hzq
              rw [← hy, ← hz] at hm hzq
              omega
        apply Subtype.ext
        apply Prod.ext
        · apply hd p.val.2
          simpa only [hy] using hsame
        · exact hy
      · simp only [F, dif_pos hp, dif_neg hq, Sum.inl_ne_inr] at hpq
    · by_cases hq : (eligible q.val).Nonempty
      · simp only [F, dif_neg hp, dif_pos hq, Sum.inr_ne_inl] at hpq
      · have hy : p.val.2 = q.val.2 := by
          simpa only [F, dif_neg hp, dif_neg hq, Sum.inr.injEq] using hpq
        have hsame : (p.val.1 - p.val.2).val = (q.val.1 - p.val.2).val := by
          by_contra hn
          rcases lt_or_gt_of_ne hn with hlt | hgt
          · cases up with
            | false =>
              apply hq
              refine ⟨p.val.1, ?_⟩
              simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by simpa only [← hy] using (hE p.val p.property).symm,
                by simpa [← hy] using hlt⟩
            | true =>
              apply hp
              refine ⟨q.val.1, ?_⟩
              simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by simpa only [hy] using (hE q.val q.property).symm, hlt⟩
          · cases up with
            | false =>
              apply hp
              refine ⟨q.val.1, ?_⟩
              simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by simpa only [hy] using (hE q.val q.property).symm, hgt⟩
            | true =>
              apply hq
              refine ⟨p.val.1, ?_⟩
              simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by simpa only [← hy] using (hE p.val p.property).symm,
                by simpa [← hy] using hgt⟩
        apply Subtype.ext
        exact Prod.ext (hd p.val.2 hsame) hy
  simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective F hF

/-- Ordered final edges admitting a forward cyclically ordered alternating path. -/
noncomputable def zigzagEnds {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => ∃ f : DihedralRamseyDefs.altPath (k + 1) →g G,
    StrictMono (fun i => ((f i) - (f 0)).val) ∧
      ∃ i j : Fin (k + 1), i.val = DihedralRamseyDefs.altVertex (k + 1) (k - 1) ∧
        j.val = DihedralRamseyDefs.altVertex (k + 1) k ∧ f i = p.1 ∧ f j = p.2

/-- The zigzag end-extension estimate of Füredi, Jiang, Kostochka, Mubayi and Verstraëte. -/
theorem extremal {a n : ℕ} (ha : 2 ≤ a) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (h : ¬ CyclicEmbeddable (DihedralRamseyDefs.altPath a) G) :
    2 * G.edgeFinset.card ≤ (a - 2) * n := by
  classical
  have hdist (x y : Fin n) : (y - x).val =
      if x.val ≤ y.val then y.val - x.val else n + y.val - x.val := by
    split_ifs with hxy
    · exact Fin.sub_val_of_le hxy
    · exact Fin.coe_sub_iff_lt.mpr (by omega)
  open DihedralRamseyDefs in
  have rank_ne : ∀ j h : ℕ, j + 1 < h → altVertex h j ≠ altVertex h (j + 1) := by
    intro j h hj
    dsimp [altVertex]
    split_ifs <;> omega
  have hmem : ∀ k p, p ∈ zigzagEnds G k ↔
      ∃ f : DihedralRamseyDefs.altPath (k + 1) →g G,
        StrictMono (fun i => ((f i) - (f 0)).val) ∧
          ∃ i j : Fin (k + 1),
            i.val = DihedralRamseyDefs.altVertex (k + 1) (k - 1) ∧
            j.val = DihedralRamseyDefs.altVertex (k + 1) k ∧ f i = p.1 ∧ f j = p.2 := by
    intro k p
    simp only [zigzagEnds, Finset.mem_filter, Finset.mem_univ, true_and]
  have hend : ∀ k, 1 ≤ k → ∀ p ∈ zigzagEnds G k, G.Adj p.1 p.2 := by
    intro k hk p hp
    obtain ⟨f, _, i, j, hi, hj, hfi, hfj⟩ := (hmem k p).mp hp
    rw [← hfi, ← hfj]
    apply f.map_adj
    change i ≠ j ∧ _
    refine ⟨?_, Or.inl ⟨k - 1, by omega, hi, ?_⟩⟩
    · intro he
      have hval := congrArg Fin.val he
      have hh := rank_ne (k - 1) (k + 1) (by omega)
      rw [hi, hj] at hval
      rw [show k - 1 + 1 = k by omega] at hh
      exact hh hval
    · simpa only [show k - 1 + 1 = k by omega] using hj
  have hbase : zigzagEnds G 1 = Finset.univ.filter (fun p => G.Adj p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hend 1 (by omega) p
    · intro hp
      let f : DihedralRamseyDefs.altPath 2 →g G :=
        { toFun := fun i => if i.val = 0 then p.1 else p.2
          map_rel' := by
            intro i j hij
            change i ≠ j ∧ _ at hij
            obtain ⟨hne, hij | hji⟩ := hij
            · obtain ⟨r, hr, hi, hj⟩ := hij
              have hr0 : r = 0 := by omega
              subst r
              change i.val = 0 at hi
              change j.val = 1 at hj
              simpa [hi, hj] using hp
            · obtain ⟨r, hr, hj, hi⟩ := hji
              have hr0 : r = 0 := by omega
              subst r
              change i.val = 1 at hi
              change j.val = 0 at hj
              simpa [hi, hj] using hp.symm }
      apply (hmem 1 p).mpr
      refine ⟨f, ?_, 0, 1, by rfl, by rfl, by rfl, by rfl⟩
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change (p.1 - p.1).val < (p.2 - p.1).val
      have hne := hp.ne
      have hval : p.1.val ≠ p.2.val := fun he => hne (Fin.ext he)
      simp only [hdist]
      split_ifs <;> omega
  have hnext : ∀ k, 1 ≤ k →
      (zigzagEnds G k).card ≤ (zigzagEnds G (k + 1)).card + n := by
    intro k hk
    apply end_extension_count G _ _ (k % 2 == 1) (hend k hk)
    intro p hp z hz harc
    obtain ⟨f, hf, i, j, hi, hj, hfi, hfj⟩ := (hmem k p).mp hp
    obtain ⟨f', hf', i', j', hi', hj', hfi', hfj'⟩ :=
      append_zigzag hk G f hf i j hi hj z (by simpa [hfj] using hz)
        (by simpa [hfi, hfj] using harc)
    exact (hmem (k + 1) (p.2, z)).mpr
      ⟨f', hf', i', j', hi', hj', hfi'.trans hfj, hfj'⟩
  have count : ∀ k, 1 ≤ k →
      2 * G.edgeFinset.card ≤ (zigzagEnds G k).card + (k - 1) * n := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        rw [hbase, ← SimpleGraph.two_mul_card_edgeFinset]
        simp
      · have hi := ih (by omega)
        have hn := hnext k (by omega)
        have he : k * n = (k - 1) * n + n := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          rw [Nat.add_mul, one_mul]
        simp only [Nat.add_sub_cancel] at *
        omega
  have hempty : zigzagEnds G (a - 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨f, hf, _, _, _, _, _, _⟩ := (hmem (a - 1) p).mp hp
    obtain ⟨s, ψ, hψ, hrep⟩ := cyclic_selection f hf
    have he : a - 1 + 1 = a := by omega
    apply h
    rw [← he]
    refine ⟨s, ψ, hψ, ?_⟩
    intro i j hij
    rw [← hrep i, ← hrep j]
    exact f.map_adj hij
  have hc := count (a - 1) (by omega)
  rw [hempty, Finset.card_empty, zero_add] at hc
  simpa only [Nat.sub_sub] using hc

end D5.S3.Combinatorics.DihedralRamsey
