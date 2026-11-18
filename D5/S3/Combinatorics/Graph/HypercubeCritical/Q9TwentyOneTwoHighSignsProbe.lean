import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighProbe

/-! The actual signed eight-cycle through an end on each side of the two-root pair. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching flip)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm switching_ne_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private spokePhase translate_spoke_phase spoke_phase_neg far_common_midpoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCenterProbe
attribute [local instance] Classical.propDecidable
open private armTypes arm_coordinates flip_direction_unique from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareExclusion
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self diff_injective diff_triangle_card adj_of_diff_subset_card low_not_three
  compressed_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-- An eight-cycle through the two roots labels its core point. Distinct
outward directions force a unique core point, and equal directions fix
the support of the intervening low vertex as well. -/
private lemma two_high_arm_label
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (hv : Function.Injective v)
    (hAdj : ∀ i, (hypercube n).Adj (v i).val (v (i + 1)).val)
    {a b c u : Fin n}
    (ha : (v 1).val = flip (v 0).val a)
    (hb' : (v 2).val = flip (v 1).val b)
    (hc : (v 3).val = flip (v 2).val c)
    (hu : (v 7).val = flip (v 0).val u) :
    let D := fun i : Fin 8 => diff (v i).val (v 0).val
    (u ≠ c ∧ D 5 = {b, c, u}) ∨
      (u = c ∧ ∃ t : Fin n, t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ D 5 = {a, c, t} ∧ D 6 = {c, t}) := by
  classical
  choose w hw using fun i => adjacent_exists_flip (hAdj i)
  obtain ⟨g, hgi, hg0, hg1, hg2, hwords⟩ := arm_coordinates hb v hv w hw
  have h0 : g 0 = a := by
    rw [← hg0]
    exact flip_direction_unique ((hw 0).symm.trans ha)
  have h1 : g 1 = b := by
    rw [← hg1]
    exact flip_direction_unique ((hw 1).symm.trans hb')
  have h2 : g 2 = c := by
    rw [← hg2]
    exact flip_direction_unique ((hw 2).symm.trans hc)
  let D := fun i : Fin 8 => diff (v i).val (v 0).val
  have huD : D 7 = {u} := by change diff (v 7).val (v 0).val = _; rw [hu, diff_flip, diff_self]; simp
  change armTypes (v 0).val (v 7).val (v 6).val (v 5).val (v 4).val
    (g 0) (g 1) (g 2) (g 3) at hwords
  have h' : armTypes (v 0).val (v 7).val (v 6).val (v 5).val (v 4).val a b c (g 3) := by
    simpa only [h0, h1, h2] using hwords
  unfold armTypes at h'
  have d_ne_a : g 3 ≠ a := h0 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 0)
  have d_ne_b : g 3 ≠ b := h1 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 1)
  have d_ne_c : g 3 ≠ c := h2 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 2)
  rcases h' with ⟨hd, _, hcore, _⟩ | ⟨hd, _, hcore, _⟩ | ⟨hd, hlow, hcore, _⟩
  · have he : u = g 3 := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inl ⟨he ▸ d_ne_c, he ▸ hcore⟩
  · have he : u = g 3 := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inl ⟨he ▸ d_ne_c, he ▸ hcore⟩
  · have he : u = c := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inr ⟨he, g 3, d_ne_a, d_ne_b, d_ne_c, hcore, hlow⟩

#print axioms two_high_arm_label

/-- Realize the signed eight-cycle from a core vertex and its two matched
neighbors. Every midpoint comes from a compressed edge of the actual graph. -/
private lemma actual_core_arm_label
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hp : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (x y : SideHigh ((hypercube n).induce (S : Set (Q n))) L)
    (u w h : SideHigh ((hypercube n).induce (S : Set (Q n))) R)
    (huw : u ≠ w) (m : (S : Set (Q n)))
    (hm : ((hypercube n).induce (S : Set (Q n))).degree m = 2)
    (hxm : ((hypercube n).induce (S : Set (Q n))).Adj x.val m)
    (hym : ((hypercube n).induce (S : Set (Q n))).Adj y.val m)
    (hxy : x ≠ y)
    (hxu : ((hypercube n).induce (S : Set (Q n))).Adj x.val u.val)
    (hyw : ((hypercube n).induce (S : Set (Q n))).Adj y.val w.val)
    (hhu : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj h u)
    (hhw : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj h w)
    {a b c d : Fin n}
    (ha : m.val = flip x.val.val a)
    (hb' : y.val.val = flip m.val b)
    (hc : w.val.val = flip y.val.val c)
    (hd : u.val.val = flip x.val.val d) :
    let D := fun v : Q n => diff v x.val.val
    (d ≠ c ∧ D h.val.val = {b, c, d}) ∨
      (d = c ∧ ∃ (t : Fin n) (p : (S : Set (Q n))),
        t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ D h.val.val = {a, c, t} ∧ D p.val = {c, t} ∧
        ((hypercube n).induce (S : Set (Q n))).degree p = 2 ∧
        ((hypercube n).induce (S : Set (Q n))).Adj h.val p ∧
        ((hypercube n).induce (S : Set (Q n))).Adj u.val p) := by
  classical
  let G := (hypercube n).induce (S : Set (Q n))
  obtain ⟨hnu, p, hp2, hhp, hup⟩ := hhu
  obtain ⟨hnw, q, hq2, hhq, hwq⟩ := hhw
  have hL (r : SideHigh G L) : r.val ∈ L := (mem_filter.mp r.property).1
  have hR (r : SideHigh G R) : r.val ∈ R := (mem_filter.mp r.property).1
  have hpL : p ∈ L := hp.mem_of_mem_adj' (hR u) hup.symm
  have hqL : q ∈ L := hp.mem_of_mem_adj' (hR w) hwq.symm
  have hmR : m ∈ R := hp.mem_of_mem_adj (hL x) hxm
  have lr {l r : (S : Set (Q n))} (hl : l ∈ L) (hr : r ∈ R) : l ≠ r :=
    fun he => Set.disjoint_left.mp hp.disjoint hl (he ▸ hr)
  have low_high {l : (S : Set (Q n))} (hl : G.degree l = 2) {r : (S : Set (Q n))}
      (hr : G.degree r = 3) : l ≠ r := by
    intro he
    rw [he, hr] at hl
    omega
  have degL (r : SideHigh G L) : G.degree r.val = 3 := (mem_filter.mp r.property).2
  have degR (r : SideHigh G R) : G.degree r.val = 3 := (mem_filter.mp r.property).2
  have hnPQ : p ≠ q := by
    intro he
    exact low_not_three hp2 (fun hx => hnu (Subtype.ext hx)) (fun hx => hnw (Subtype.ext hx))
      (fun hx => huw (Subtype.ext hx)) hhp.symm hup.symm (he ▸ hwq.symm)
  let v : Fin 8 → (S : Set (Q n)) := ![x.val, m, y.val, w.val, q, h.val, p, u.val]
  have hv : Function.Injective v := by
    apply List.nodup_ofFn.mp
    change [x.val, m, y.val, w.val, q, h.val, p, u.val].Nodup
    have h01 : x.val ≠ m := lr (hL x) hmR
    have h02 : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    have h03 : x.val ≠ w.val := lr (hL x) (hR w)
    have h04 : x.val ≠ q := Ne.symm (low_high hq2 (degL x))
    have h05 : x.val ≠ h.val := lr (hL x) (hR h)
    have h06 : x.val ≠ p := Ne.symm (low_high hp2 (degL x))
    have h07 : x.val ≠ u.val := lr (hL x) (hR u)
    have h12 : m ≠ y.val := Ne.symm (lr (hL y) hmR)
    have h13 : m ≠ w.val := low_high hm (degR w)
    have h14 : m ≠ q := Ne.symm (lr hqL hmR)
    have h15 : m ≠ h.val := low_high hm (degR h)
    have h16 : m ≠ p := Ne.symm (lr hpL hmR)
    have h17 : m ≠ u.val := low_high hm (degR u)
    have h23 : y.val ≠ w.val := lr (hL y) (hR w)
    have h24 : y.val ≠ q := Ne.symm (low_high hq2 (degL y))
    have h25 : y.val ≠ h.val := lr (hL y) (hR h)
    have h26 : y.val ≠ p := Ne.symm (low_high hp2 (degL y))
    have h27 : y.val ≠ u.val := lr (hL y) (hR u)
    have h34 : w.val ≠ q := Ne.symm (lr hqL (hR w))
    have h35 : w.val ≠ h.val := fun he => hnw (Subtype.ext he.symm)
    have h36 : w.val ≠ p := Ne.symm (lr hpL (hR w))
    have h37 : w.val ≠ u.val := fun he => huw (Subtype.ext he.symm)
    have h45 : q ≠ h.val := lr hqL (hR h)
    have h46 : q ≠ p := Ne.symm hnPQ
    have h47 : q ≠ u.val := lr hqL (hR u)
    have h56 : h.val ≠ p := Ne.symm (lr hpL (hR h))
    have h57 : h.val ≠ u.val := fun he => hnu (Subtype.ext he)
    have h67 : p ≠ u.val := lr hpL (hR u)
    simp [List.nodup_cons, h01, h02, h03, h04, h05, h06, h07, h12, h13, h14, h15, h16, h17, h23, h24, h25, h26, h27, h34, h35, h36, h37, h45, h46, h47, h56, h57, h67]
  have hvAdj (i : Fin 8) : G.Adj (v i) (v (i + 1)) := by
    fin_cases i
    · exact hxm
    · exact hym.symm
    · exact hyw
    · exact hwq
    · exact hhq.symm
    · exact hhp
    · exact hup.symm
    · exact hxu.symm
  rcases two_high_arm_label hb v hv hvAdj ha hb' hc hd with h | ⟨he, t, hta, htb, htc, hcore, hp'⟩
  · exact Or.inl h
  · exact Or.inr ⟨he, t, p, hta, htb, htc, hcore, hp', hp2, hhp, hup⟩

#print axioms actual_core_arm_label

/-- Distance two from an unequal-direction core would give the low
neighbor of an equal-direction core a third neighbor. -/
private lemma equal_direction_core_not_distance_two_from_distinct
    {n : ℕ} {S : Finset (Q n)} (x : Q n) {a b c t d e : Fin n}
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (m u v w : (S : Set (Q n)))
    (hm : diff m.val x = {c, t})
    (hv : diff v.val x = {a, c, t}) (hw : diff w.val x = {b, d, e})
    (hm2 : ((hypercube n).induce (S : Set (Q n))).degree m = 2)
    (hmu : ((hypercube n).induce (S : Set (Q n))).Adj m u)
    (hmv : ((hypercube n).induce (S : Set (Q n))).Adj m v)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    hammingDist v.val w.val ≠ 2 := by
  intro hdist
  have hcount := diff_triangle_card v.val w.val x
  change hammingDist v.val w.val + 2 * _ = _ at hcount
  rw [hdist, hv, hw] at hcount
  have hcardV : ({a, c, t} : Finset (Fin n)).card = 3 := by simp [hac, hat, hct]
  have hcardW : ({b, d, e} : Finset (Fin n)).card = 3 := by simp [hbd, hbe, hde]
  rw [hcardV, hcardW] at hcount
  have hcard : (({a, c, t} : Finset (Fin n)) ∩ {b, d, e}).card = 2 := by omega
  have hsub : ({a, c, t} : Finset (Fin n)) ∩ {b, d, e} ⊆ {c, t} := by
    intro i hi
    obtain ⟨hl, hr⟩ := mem_inter.mp hi
    have hia : i ≠ a := by
      rintro rfl
      simp [hab, had, hae] at hr
    simpa only [mem_insert, hia, false_or] using hl
  have hpair : ({a, c, t} : Finset (Fin n)) ∩ {b, d, e} = {c, t} :=
    eq_of_subset_of_card_le hsub (by simp [hcard, hct])
  have hsub' : diff m.val x ⊆ diff w.val x := by
    rw [hm, hw, ← hpair]
    exact inter_subset_right
  have hmw : ((hypercube n).induce (S : Set (Q n))).Adj m w :=
    adj_of_diff_subset_card hsub' (by simp [hm, hw, hct, hcardW])
  exact low_not_three hm2 huv huw hvw hmu hmv hmw

#print axioms equal_direction_core_not_distance_two_from_distinct

private lemma equal_spoke_phase_at_center
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) {x : Q n} (hx : x ∈ S)
    {c d : Fin n} (hc : flip x c ∈ S) (hd : flip x d ∈ S) :
    spokePhase sigma x c = spokePhase sigma x d := by
  have phase (r : Fin n) (hr : flip x r ∈ S) : spokePhase sigma x r = sigma x := by
    unfold spokePhase
    rw [hs.2 x hx _ hr (BalancedCriticalSpectrum.flip_adj _ _), mul_assoc,
      ← pow_two, switching_sq hs hr, mul_one]
  exact (phase c hc).trans (phase d hd).symm

private lemma equal_phase_forces_middle
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) {x : Q n} {c d : Fin n} (hcd : c ≠ d)
    (hc : flip x c ∈ S) (hd : flip x d ∈ S)
    (hphase : spokePhase sigma x c = spokePhase sigma x d)
    {m : Q n} (hm : m ∈ S)
    (hcm : (hypercube n).Adj (flip x c) m)
    (hdm : (hypercube n).Adj (flip x d) m) : m = x := by
  by_contra hne
  have hfar := far_common_midpoint hcd hne hcm hdm
  have hsign := spoke_phase_neg hs x hcd hc hd (hfar ▸ hm)
  have hzero : spokePhase sigma x c = 0 := by linarith
  have hsq := SupportedEigenSaturation.matrix_sq_of_adj (BalancedCriticalSpectrum.flip_adj x c)
  have hnon : huangMatrix n x (flip x c) ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  exact mul_ne_zero hnon (switching_ne_zero hs hc) hzero

/-- A common midpoint after one parallel translation of two selected spokes
has a third selected neighbor, namely the original center. -/
private lemma translated_spokes_middle_not_degree_two
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (x : Q n) {c d t : Fin n}
    (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t)
    (hx : x ∈ S) (hc : flip x c ∈ S) (hd : flip x d ∈ S)
    (hctS : flip (flip x t) c ∈ S) (hdtS : flip (flip x t) d ∈ S)
    (m : (S : Set (Q n)))
    (hcm : (hypercube n).Adj (flip (flip x t) c) m.val)
    (hdm : (hypercube n).Adj (flip (flip x t) d) m.val) :
    ((hypercube n).induce (S : Set (Q n))).degree m ≠ 2 := by
  classical
  have hbase := equal_spoke_phase_at_center hs hx hc hd
  have hphase : spokePhase sigma (flip x t) c = spokePhase sigma (flip x t) d := by
    rw [translate_spoke_phase hs x hct hc hctS, translate_spoke_phase hs x hdt hd hdtS, hbase]
  have hm := equal_phase_forces_middle hs hcd hctS hdtS hphase m.property hcm hdm
  let u : (S : Set (Q n)) := ⟨x, hx⟩
  let v : (S : Set (Q n)) := ⟨flip (flip x t) c, hctS⟩
  let w : (S : Set (Q n)) := ⟨flip (flip x t) d, hdtS⟩
  have hmu : ((hypercube n).induce (S : Set (Q n))).Adj m u := by
    change (hypercube n).Adj m.val x
    rw [hm]
    exact (BalancedCriticalSpectrum.flip_adj x t).symm
  have huv : u ≠ v := by
    intro h
    have he : flip (flip x t) t = flip (flip x t) c := by
      simpa [u, v] using congrArg Subtype.val h
    exact hct (flip_direction_unique he).symm
  have huw : u ≠ w := by
    intro h
    have he : flip (flip x t) t = flip (flip x t) d := by
      simpa [u, w] using congrArg Subtype.val h
    exact hdt (flip_direction_unique he).symm
  have hvw : v ≠ w := fun h => hcd (flip_direction_unique (congrArg Subtype.val h))
  exact fun hm2 => low_not_three hm2 huv huw hvw hmu hcm.symm hdm.symm

/-- Starting at a selected center, two parallel translations preserve equal
spoke phase. A selected middle of the final spokes must be their center. -/
private lemma doubly_translated_spokes_middle
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (x : Q n) {c d t a : Fin n}
    (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) (hca : c ≠ a) (hda : d ≠ a)
    (hx : x ∈ S) (hc : flip x c ∈ S) (hd : flip x d ∈ S)
    (hctS : flip (flip x t) c ∈ S) (hdtS : flip (flip x t) d ∈ S)
    (hcaS : flip (flip (flip x t) a) c ∈ S) (hdaS : flip (flip (flip x t) a) d ∈ S)
    {m : Q n} (hm : m ∈ S)
    (hcm : (hypercube n).Adj (flip (flip (flip x t) a) c) m)
    (hdm : (hypercube n).Adj (flip (flip (flip x t) a) d) m) :
    m = flip (flip x t) a := by
  let z := flip (flip x t) a
  have hbase := equal_spoke_phase_at_center hs hx hc hd
  have hfirst : spokePhase sigma (flip x t) c = spokePhase sigma (flip x t) d := by
    rw [translate_spoke_phase hs x hct hc hctS, translate_spoke_phase hs x hdt hd hdtS, hbase]
  have hlast : spokePhase sigma z c = spokePhase sigma z d := by
    dsimp [z]
    rw [translate_spoke_phase hs _ hca hctS hcaS, translate_spoke_phase hs _ hda hdtS hdaS, hfirst]
  exact equal_phase_forces_middle hs hcd hcaS hdaS hlast hm hcm hdm

/-- When the root midpoint is already low, the center forced by two
translations cannot also be low. -/
private lemma doubly_translated_spokes_excludes_low_middle
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (x : Q n) {c d t a : Fin n}
    (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) (hca : c ≠ a) (hda : d ≠ a)
    (hx : x ∈ S) (hc : flip x c ∈ S) (hd : flip x d ∈ S)
    (hctS : flip (flip x t) c ∈ S) (hdtS : flip (flip x t) d ∈ S)
    (hcaS : flip (flip (flip x t) a) c ∈ S) (hdaS : flip (flip (flip x t) a) d ∈ S)
    (r m : (S : Set (Q n))) (hr : r.val = flip x a)
    (hr2 : ((hypercube n).induce (S : Set (Q n))).degree r = 2)
    (hcm : (hypercube n).Adj (flip (flip (flip x t) a) c) m.val)
    (hdm : (hypercube n).Adj (flip (flip (flip x t) a) d) m.val)
    (hlow : ∀ ⦃v w⦄, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False) :
    ((hypercube n).induce (S : Set (Q n))).degree m ≠ 2 := by
  have hm := doubly_translated_spokes_middle hs x hcd hct hdt hca hda hx hc hd
    hctS hdtS hcaS hdaS m.property hcm hdm
  have hadj : ((hypercube n).induce (S : Set (Q n))).Adj r m := by
    change (hypercube n).Adj r.val m.val
    rw [hr, hm, flip_comm x t a]
    exact BalancedCriticalSpectrum.flip_adj _ _
  exact hlow hadj hr2

#print axioms translated_spokes_middle_not_degree_two
#print axioms doubly_translated_spokes_middle
#print axioms doubly_translated_spokes_excludes_low_middle

private lemma diff_two_flips {n : ℕ} (x : Q n) {a b : Fin n} (hab : a ≠ b) :
    diff (flip (flip x a) b) x = {a, b} := by
  rw [diff_flip, diff_flip, diff_self]
  simp [hab.symm, pair_comm]

private lemma diff_three_flips {n : ℕ} (x : Q n) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    diff (flip (flip (flip x a) b) c) x = {a, b, c} := by
  rw [diff_flip, diff_two_flips x hab]
  have hnot : c ∉ ({a, b} : Finset (Fin n)) := by simp [hac.symm, hbc.symm]
  rw [if_neg hnot]
  ext i
  simp only [mem_insert, mem_singleton]
  tauto

/-- A degree-two midpoint with support `{c,t}` on the arm through
`{c}` excludes a second selected end in direction `t`. -/
private lemma equal_arm_parameter_avoids_other_end
    {n : ℕ} {S : Finset (Q n)} (x : Q n) {a c t : Fin n}
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t)
    (v p : (S : Set (Q n))) (hv : diff v.val x = {a, c, t})
    (hp : diff p.val x = {c, t})
    (hp2 : ((hypercube n).induce (S : Set (Q n))).degree p = 2)
    (hc : flip x c ∈ S) (ht : flip x t ∈ S) : False := by
  classical
  let u : (S : Set (Q n)) := ⟨flip x c, hc⟩
  let w : (S : Set (Q n)) := ⟨flip x t, ht⟩
  have hU : diff u.val x = {c} := by
    change diff (flip x c) x = _
    simp [diff_flip, diff_self]
  have hW : diff w.val x = {t} := by
    change diff (flip x t) x = _
    simp [diff_flip, diff_self]
  have hcardP : (diff p.val x).card = 2 := by simp [hp, hct]
  have hcardV : (diff v.val x).card = 3 := by simp [hv, hac, hat, hct]
  have hcardU : (diff u.val x).card = 1 := by simp [hU]
  have hcardW : (diff w.val x).card = 1 := by simp [hW]
  have hpu : (hypercube n).Adj u.val p.val :=
    adj_of_diff_subset_card (o := x) (by simp [hU, hp]) (by omega)
  have hpw : (hypercube n).Adj w.val p.val :=
    adj_of_diff_subset_card (o := x) (by simp [hW, hp]) (by omega)
  have hpv : (hypercube n).Adj p.val v.val :=
    adj_of_diff_subset_card (by rw [hp, hv]; exact subset_insert _ _) (by omega)
  have hne {f g : (S : Set (Q n))} (h : f = g) :
      (diff f.val x).card = (diff g.val x).card := by rw [h]
  exact low_not_three hp2
    (fun h : u = w => hct (flip_direction_unique (congrArg Subtype.val h)))
    (fun h : u = v => by have he := hne h; omega)
    (fun h : w = v => by have he := hne h; omega) hpu.symm hpw.symm hpv

/-- Two cores with equal directions on their respective arms cannot be
matched. A translation pins the midpoint within a row, and two translations
pin it across rows. -/
private lemma equal_direction_cores_not_matched
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) {x : Q n} (hx : x ∈ S)
    {a c d t s : Fin n} (hac : a ≠ c) (had : a ≠ d)
    (hat : a ≠ t) (has : a ≠ s) (hct : c ≠ t) (hds : d ≠ s)
    (hc : flip x c ∈ S) (hd : flip x d ∈ S)
    (v w p q r m : (S : Set (Q n)))
    (hv : diff v.val x = {a, c, t}) (hw : diff w.val x = {a, d, s})
    (hp : diff p.val x = {c, t}) (hq : diff q.val x = {d, s})
    (hp2 : ((hypercube n).induce (S : Set (Q n))).degree p = 2)
    (hq2 : ((hypercube n).induce (S : Set (Q n))).degree q = 2)
    (hr : r.val = flip x a)
    (hr2 : ((hypercube n).induce (S : Set (Q n))).degree r = 2)
    (hm2 : ((hypercube n).induce (S : Set (Q n))).degree m = 2)
    (hvm : (hypercube n).Adj v.val m.val) (hwm : (hypercube n).Adj w.val m.val)
    (hvw : hammingDist v.val w.val = 2)
    (hlow : ∀ ⦃v w⦄, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False) : False := by
  classical
  by_cases hcd : c = d
  · subst d
    have hts : t ≠ s := by
      intro he
      have h := diff_injective x (hv.trans (he ▸ hw.symm))
      simp [h] at hvw
    have hp' : p.val = flip (flip x c) t :=
      diff_injective x (hp.trans (diff_two_flips x hct).symm)
    have hq' : q.val = flip (flip x c) s :=
      diff_injective x (hq.trans (diff_two_flips x hds).symm)
    have hv' : v.val = flip (flip (flip x c) a) t := by
      apply diff_injective x
      change diff v.val x = diff (flip (flip (flip x c) a) t) x
      rw [hv, diff_three_flips x hac.symm hct hat, insert_comm]
    have hw' : w.val = flip (flip (flip x c) a) s := by
      apply diff_injective x
      change diff w.val x = diff (flip (flip (flip x c) a) s) x
      rw [hw, diff_three_flips x hac.symm hds has, insert_comm]
    exact translated_spokes_middle_not_degree_two hs (flip x c) hts hat.symm has.symm hc
      (hp' ▸ p.property) (hq' ▸ q.property) (hv' ▸ v.property) (hw' ▸ w.property) m
      (hv' ▸ hvm) (hw' ▸ hwm) hm2
  · have hdt : d ≠ t := by
      intro he
      exact equal_arm_parameter_avoids_other_end x hac hat hct v p hv hp hp2 hc (he ▸ hd)
    have hcs : c ≠ s := by
      intro he
      exact equal_arm_parameter_avoids_other_end x had has hds w q hw hq hq2 hd (he ▸ hc)
    have hts : t = s := by
      by_contra hne
      have hEq : ({a, c, t} : Finset (Fin n)) ∩ {a, d, s} = {a} := by
        ext i
        simp only [mem_inter, mem_insert, mem_singleton]
        aesop
      have h := diff_triangle_card v.val w.val x
      change hammingDist v.val w.val + 2 * _ = _ at h
      rw [hvw, hv, hw, hEq] at h
      simp [hac, hat, hct, had, has, hds] at h
    subst s
    have hp' : p.val = flip (flip x t) c := by
      apply diff_injective x
      change diff p.val x = diff (flip (flip x t) c) x
      rw [hp, diff_two_flips x hct.symm, pair_comm]
    have hq' : q.val = flip (flip x t) d := by
      apply diff_injective x
      change diff q.val x = diff (flip (flip x t) d) x
      rw [hq, diff_two_flips x hds.symm, pair_comm]
    have hv' : v.val = flip (flip (flip x t) a) c := by
      apply diff_injective x
      change diff v.val x = diff (flip (flip (flip x t) a) c) x
      rw [hv, diff_three_flips x hat.symm hct.symm hac]
      ext i
      simp only [mem_insert, mem_singleton]
      tauto
    have hw' : w.val = flip (flip (flip x t) a) d := by
      apply diff_injective x
      change diff w.val x = diff (flip (flip (flip x t) a) d) x
      rw [hw, diff_three_flips x hat.symm hds.symm had]
      ext i
      simp only [mem_insert, mem_singleton]
      tauto
    exact doubly_translated_spokes_excludes_low_middle hs x hcd hct hds hac.symm had.symm
      hx hc hd (hp' ▸ p.property) (hq' ▸ q.property) (hv' ▸ v.property) (hw' ▸ w.property)
      r m hr hr2 (hv' ▸ hvm) (hw' ▸ hwm) hlow hm2

#print axioms equal_direction_cores_not_matched

set_option maxHeartbeats 600000 in
/-- Once the actual core matching is available, every arm has distinct
directions. An equal arm can have neither kind of matching partner. -/
private lemma matched_core_arm_label
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hp : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (x y : SideHigh ((hypercube n).induce (S : Set (Q n))) L)
    (hxy : x ≠ y) (m : (S : Set (Q n)))
    (hm2 : ((hypercube n).induce (S : Set (Q n))).degree m = 2)
    (hxm : ((hypercube n).induce (S : Set (Q n))).Adj x.val m)
    (hym : ((hypercube n).induce (S : Set (Q n))).Adj y.val m)
    (hlow : ∀ ⦃v w⦄, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    {a b : Fin n} (hab : a ≠ b)
    (hm : m.val = flip x.val.val a) (hy : y.val.val = flip m.val b) :
    let G := (hypercube n).induce (S : Set (Q n))
    let K := compressed G R
    ∀ {u w v u' w' v' : SideHigh G R} {c d c' d' : Fin n},
      u ≠ w → u' ≠ w' → u ≠ v' →
      G.Adj x.val u.val → G.Adj y.val w.val → G.Adj x.val u'.val → G.Adj y.val w'.val →
      K.Adj v u → K.Adj v w → K.Adj v' u' → K.Adj v' w' → K.Adj v v' →
      w.val.val = flip y.val.val c → u.val.val = flip x.val.val d →
      w'.val.val = flip y.val.val c' → u'.val.val = flip x.val.val d' →
      a ≠ c → a ≠ c' → a ≠ d' → b ≠ c' → b ≠ d' →
      d ≠ c ∧ diff v.val.val x.val.val = {b, c, d} := by
  classical
  dsimp only
  intro u w v u' w' v' c d c' d' huw huw' huv' hxu hyw hxu' hyw'
    hvu hvw hvu' hvw' hvv' hw hu hw' hu' hac hac' had' hbc' hbd'
  rcases actual_core_arm_label hb hp x y u w v huw m hm2 hxm hym hxy hxu hyw hvu hvw
      hm hy hw hu with h | ⟨he, t, p, hta, _, htc, hv, hp'⟩
  · exact h
  · obtain ⟨hpDiff, hp2, hvp, hup⟩ := hp'
    obtain ⟨sigma, hs⟩ := hb
    have hdist := compressed_distance hvv'
    rcases actual_core_arm_label ⟨sigma, hs⟩ hp x y u' w' v' huw' m hm2 hxm hym hxy
        hxu' hyw' hvu' hvw' hm hy hw' hu' with h | h
    · exfalso
      exact equal_direction_core_not_distance_two_from_distinct (S := S) x.val.val hac
        hta.symm htc.symm hab hac' had' hbc' hbd' h.1.symm
        p u.val v.val v'.val hpDiff hv h.2 hp2 hup.symm hvp.symm
        (fun e => hvu.ne (Subtype.ext e.symm)) (fun e => huv' (Subtype.ext e))
        (fun e => hvv'.ne (Subtype.ext e)) hdist
    · obtain ⟨he', s, q, hsa, _, hsc, hv', hq, hq2, _, _⟩ := h
      obtain ⟨_, k, hk2, hvk, hv'k⟩ := hvv'
      exfalso
      exact equal_direction_cores_not_matched (S := S) hs x.val.property hac hac'
        hta.symm hsa.symm htc.symm hsc.symm
        (by rw [← he, ← hu]; exact u.val.property)
        (by rw [← he', ← hu']; exact u'.val.property)
        v.val v'.val p q m k hv hv' hpDiff hq hp2 hq2 hm hm2 hk2 hvk hv'k hdist hlow

#print axioms matched_core_arm_label
