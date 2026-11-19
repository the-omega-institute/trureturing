/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthLeafSignProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthLeafSignProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Huang balance fixes the order of the middle directions of a four-step walk when the first and last directions coincide. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthNeighborhoodProbe

/-! A Huang-balanced four-step walk fixes the order of the two middle directions
when the first and last directions coincide. -/

set_option autoImplicit false

noncomputable section

open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip gamma IsSwitching IsBalanced)
open private coeff gammaV gammaV_zero gammaV_succ switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private gamma_three_switching switching_ne_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private lemma gamma_involution {n : ℕ} (i : Fin n) (f : Q n → ℝ) :
    gamma i (gamma i f) = f := by
  have hV : ∀ (m : ℕ) (j : Fin m) (v : Sensitivity.V m), gammaV m j (gammaV m j v) = v := by
    intro m
    induction m with
    | zero => intro j; exact Fin.elim0 j
    | succ m ih =>
      intro j v
      induction j using Fin.cases with
      | zero =>
        rw [gammaV_zero, gammaV_zero]
        rfl
      | succ j =>
        rw [gammaV_succ, gammaV_succ]
        apply Prod.ext
        · exact ih j v.1
        · simp only [map_neg, neg_neg]
          exact ih j v.2
  change coeff n (gammaV n i ((coeff n).symm (coeff n (gammaV n i ((coeff n).symm f))))) = f
  rw [(coeff n).symm_apply_apply, hV, (coeff n).apply_symm_apply]

private lemma gamma_outer_cancel {n : ℕ} {a p q : Fin n}
    (hap : a ≠ p) (haq : a ≠ q) (f : Q n → ℝ) :
    gamma a (gamma p (gamma q (gamma a f))) = gamma p (gamma q f) := by
  rw [BalancedCubeGirth.gamma_anticommute hap, BalancedCubeGirth.gamma_anticommute haq,
    map_neg, neg_neg, gamma_involution]

private lemma gamma_four_switching {n : ℕ} {C : Finset (Q n)}
    {sigma : Q n → ℝ} (hs : IsSwitching C sigma)
    (x : Q n) (a p q b : Fin n)
    (hx : x ∈ C) (h₁ : flip x a ∈ C)
    (h₂ : flip (flip x a) p ∈ C) (h₃ : flip (flip (flip x a) p) q ∈ C)
    (h₄ : flip (flip (flip (flip x a) p) q) b ∈ C) :
    gamma a (gamma p (gamma q (gamma b (fun _ => 1)))) x =
      sigma x * sigma (flip (flip (flip (flip x a) p) q) b) := by
  rw [BalancedCriticalSpectrum.gamma_apply,
      gamma_three_switching hs _ p q b h₁ h₂ h₃ h₄,
      hs.2 _ hx _ h₁ (BalancedCriticalSpectrum.flip_adj x a)]
  calc
    _ = (sigma x * sigma (flip (flip (flip (flip x a) p) q) b)) *
        sigma (flip x a)^2 := by ring
    _ = _ := by rw [switching_sq hs h₁, mul_one]

private lemma no_oppositely_ordered_middle {n : ℕ} {C : Finset (Q n)}
    (hb : IsBalanced C) {x : Q n} {a b p q : Fin n}
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (hx : x ∈ C)
    (ha₁ : flip x a ∈ C) (ha₂ : flip (flip x a) p ∈ C)
    (ha₃ : flip (flip (flip x a) p) q ∈ C)
    (ha₄ : flip (flip (flip (flip x a) p) q) a ∈ C)
    (hb₁ : flip x b ∈ C) (hb₂ : flip (flip x b) q ∈ C)
    (hb₃ : flip (flip (flip x b) q) p ∈ C)
    (he : flip (flip (flip (flip x a) p) q) a = flip (flip (flip (flip x b) q) p) b) :
    False := by
  have hb₄ := he ▸ ha₄
  obtain ⟨sigma, hs⟩ := hb
  have h :=
    congrFun (BalancedCubeGirth.gamma_anticommute hpq (fun _ => (1 : ℝ))) x
  rw [← gamma_outer_cancel hap haq, ← gamma_outer_cancel hbq hbp] at h
  simp only [Pi.neg_apply] at h
  rw [gamma_four_switching hs x a p q a hx ha₁ ha₂ ha₃ ha₄,
    gamma_four_switching hs x b q p b hx hb₁ hb₂ hb₃ hb₄, ← he] at h
  exact (mul_ne_zero (switching_ne_zero hs hx) (switching_ne_zero hs ha₄)) (by linarith)

#print axioms no_oppositely_ordered_middle

open D5.S3.Combinatorics.Graph.Hypercube
open private flip_comm no_selected_reverse_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private agree_of_near_geodesic from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

private lemma four_step_directions_in_difference (r w : Q 9)
    (h₄ : hammingDist r w = 4) (i p q : Fin 9)
    (h : (hypercube 9).Adj (flip (flip (flip r i) p) q) w) :
    i ∈ diff r w ∧ p ∈ diff r w ∧ q ∈ diff r w := by
  let a := flip r i
  let b := flip a p
  let c := flip b q
  have hra : hammingDist r a = 1 := BalancedCriticalSpectrum.flip_adj _ _
  have hab : hammingDist a b = 1 := BalancedCriticalSpectrum.flip_adj _ _
  have hbc : hammingDist b c = 1 := BalancedCriticalSpectrum.flip_adj _ _
  have hcw : hammingDist c w = 1 := h
  have hbw : hammingDist b w ≤ 2 := by
    have := hammingDist_triangle b c w
    omega
  have haw : hammingDist a w ≤ 3 := by
    have := hammingDist_triangle a b w
    omega
  have hrb : hammingDist r b ≤ 2 := by
    have := hammingDist_triangle r a b
    omega
  have hrc : hammingDist r c ≤ 3 := by
    have := hammingDist_triangle r b c
    omega
  have agree (y : Q 9) (hy : hammingDist r y + hammingDist y w ≤ 4)
      (j : Fin 9) (hj : j ∉ diff r w) : y j = r j := by
    apply agree_of_near_geodesic h₄ ?_ j
    · simpa [diff] using hj
    · rw [hammingDist_comm w y]
      omega
  have step (y : Q 9) (j : Fin 9)
      (hy : hammingDist r y + hammingDist y w ≤ 4)
      (hy' : hammingDist r (flip y j) + hammingDist (flip y j) w ≤ 4) :
      j ∈ diff r w := by
    by_contra hn
    have hyj := agree y hy j hn
    have hyj' := agree (flip y j) hy' j hn
    have hne : (flip y j) j ≠ y j := by
      rw [BalancedCriticalSpectrum.flip_apply_same]
      cases y j <;> decide
    exact hne (hyj'.trans hyj.symm)
  exact ⟨step r i (by simp [h₄]) (by change hammingDist r a + hammingDist a w ≤ 4; omega),
    step a p (by omega) (by change hammingDist r b + hammingDist b w ≤ 4; omega),
    step b q (by omega) (by change hammingDist r c + hammingDist c w ≤ 4; omega)⟩

private lemma no_four_distance_with_all_branches {C : Finset (Q 9)}
    (hb : IsBalanced C) {r w : Q 9} (hr : r ∈ C)
    (I : Finset (Fin 9)) (hI : I.card = 3)
    (hfirst : ∀ i ∈ I, flip r i ∈ C)
    (hbranches : ∀ i ∈ I, ∃ p q : Fin 9, i ≠ p ∧ p ≠ q ∧
      flip (flip r i) p ∈ C ∧ flip (flip (flip r i) p) q ∈ C ∧
      (hypercube 9).Adj (flip (flip (flip r i) p) q) w) :
    hammingDist r w ≠ 4 := by
  intro hd
  let D := diff r w
  have hD : D.card = 4 := hd
  have hsub : I ⊆ D := by
    intro i hi
    obtain ⟨p,q,_,_,_,_,h⟩ := hbranches i hi
    exact (four_step_directions_in_difference r w hd i p q h).1
  have hsingle : (D \ I).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hI, hD]
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hsingle
  have hparent {i p : Fin 9} (hi : i ∈ I) (hip : i ≠ p) (hp : p ∈ D)
      (h : flip (flip r i) p ∈ C) : p = k := by
    have hnot : p ∉ I := by
      intro hpI
      exact BalancedCubeGirth.no_selected_square hb hip hr (hfirst i hi) (hfirst p hpI) h
    have hm : p ∈ D \ I := Finset.mem_sdiff.mpr ⟨hp,hnot⟩
    simpa [hk] using hm
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  obtain ⟨p,q,hip,hpq,hi₂,hi₃,hend⟩ := hbranches i hi
  obtain ⟨_,hpD,hqD⟩ := four_step_directions_in_difference r w hd i p q hend
  have hpk := hparent hi hip hpD hi₂
  have hqI : q ∈ I := by
    by_contra h
    have hm : q ∈ D \ I := Finset.mem_sdiff.mpr ⟨hqD,h⟩
    have : q = k := by simpa [hk] using hm
    exact hpq (hpk.trans this.symm)
  obtain ⟨p',q',hqp',_,hq₂,_,hend'⟩ := hbranches q hqI
  have hp'D := (four_step_directions_in_difference r w hd q p' q' hend').2.1
  have hpp' : p = p' := hpk.trans (hparent hqI hqp' hp'D hq₂).symm
  subst p'
  have hiq := BalancedCubeGirth.three_directions_distinct hb hip hpq hr
    (hfirst i hi) hi₂ hi₃
  have he : flip (flip (flip r i) p) q = flip (flip (flip r q) p) i := by
    calc
      _ = flip (flip (flip r i) q) p := flip_comm _ _ _
      _ = flip (flip (flip r q) i) p := by rw [flip_comm r i q]
      _ = _ := flip_comm _ _ _
  exact no_selected_reverse_three hb hip hiq hpq hr (hfirst i hi) hi₂ hi₃
    (hfirst q hqI) hq₂ (he ▸ hi₃) he

#print axioms no_four_distance_with_all_branches

open SimpleGraph
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private TwentyFourLayerRegularity.second third third_witness from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private endpoint_eq_of_short_paths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions regular_directions)
open private adjacent_exists_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private third_distance distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private lemma paths_in_all_root_directions {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x w : (C : Set (Q 9)))
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3) :
    ∀ i : Fin 9, flip x.val i ∈ C → ∃ p q : Fin 9, i ≠ p ∧ p ≠ q ∧
      flip (flip x.val i) p ∈ C ∧ flip (flip (flip x.val i) p) q ∈ C ∧
      (hypercube 9).Adj (flip (flip (flip x.val i) p) q) w.val := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let L := (third G x).filter (fun z => (hypercube 9).Adj z.val w.val)
  have hc : L.card = 3 := hfull
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hWitness (z : L) : ∃ a b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b z.val ∧
      x ≠ b ∧ a ≠ z.val ∧ b ∈ TwentyFourLayerRegularity.second G x ∧
      z.val ∉ G.neighborFinset x := third_witness (Finset.mem_filter.mp z.property).1
  choose a b ha hab hbc hxb hac hbmem hcnot using hWitness
  have hzw (z : L) : G.Adj z.val w := (Finset.mem_filter.mp z.property).2
  have haout (z : L) : a z ≠ w := by
    intro he
    apply hout
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_union_left _
      ((G.mem_neighborFinset _ _).mpr (ha z)))
  have hbout (z : L) : b z ≠ w := by
    intro he
    apply hout
    rw [← he]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hbmem z))
  let walk (z : L) : G.Walk (a z) w := .cons (hab z) (.cons (hbc z) (.cons (hzw z) .nil))
  have hpath (z : L) : (walk z).IsPath := by
    simp [walk, Walk.cons_isPath_iff, (hab z).ne, (hbc z).ne,
      (hzw z).ne, hac z, haout z, hbout z]
  let branch (z : L) : (G.neighborFinset x : Finset _) :=
    ⟨a z, (G.mem_neighborFinset _ _).mpr (ha z)⟩
  have hinj : Function.Injective branch := by
    intro z z' he
    have hza : a z = a z' := congrArg Subtype.val he
    let p : G.Walk (a z) w := walk z
    let q : G.Walk (a z) w := (walk z').copy hza.symm rfl
    have hp : p.IsPath := hpath z
    have hq : q.IsPath := by simpa [q] using hpath z'
    have hlen : p.length + q.length ≤ 6 := by simp [p, q, walk]
    have heq := endpoint_eq_of_short_paths hg hp hq hlen
    have hs := congrArg Walk.support heq
    have hvertices : a z = a z' ∧ b z = b z' ∧ z = z' := by
      simpa [p, q, walk] using hs
    exact hvertices.2.2
  have honto : Function.Surjective branch := by
    apply ((Fintype.bijective_iff_injective_and_card branch).mpr ⟨hinj, ?_⟩).2
    rw [Fintype.card_coe, Fintype.card_coe, hc, G.card_neighborFinset_eq_degree, hr.degree_eq]
  intro i hm
  let y : (C : Set (Q 9)) := ⟨flip x.val i,hm⟩
  have hy : G.Adj x y := BalancedCriticalSpectrum.flip_adj _ _
  obtain ⟨z,haz⟩ := honto ⟨y,(G.mem_neighborFinset _ _).mpr hy⟩
  have hae : a z = y := congrArg Subtype.val haz
  have hab' : (hypercube 9).Adj (flip x.val i) (b z).val := by
    have hh := hab z
    rw [hae] at hh
    exact hh
  obtain ⟨p,hp⟩ := adjacent_exists_flip hab'
  have hbc' : (hypercube 9).Adj (b z).val z.val.val := hbc z
  obtain ⟨q,hq⟩ := adjacent_exists_flip hbc'
  have hq' : z.val.val = flip (flip (flip x.val i) p) q := hq.trans (by rw [hp])
  refine ⟨p,q,?_,?_,hp ▸ (b z).property,hq' ▸ z.val.property,hq' ▸ hzw z⟩
  · intro he
    subst p
    apply hxb z
    exact Subtype.ext (by simpa [BalancedCriticalSpectrum.flip_flip] using hp.symm)
  · intro he
    subst q
    apply hac z
    apply Subtype.ext
    rw [hae]
    simpa [y, BalancedCriticalSpectrum.flip_flip] using hq'.symm

private lemma full_attachment_distance_two {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x w : (C : Set (Q 9)))
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3) :
    hammingDist x.val w.val = 2 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let L := (third G x).filter (fun z => (hypercube 9).Adj z.val w.val)
  let I := directions C x.val
  have hc : L.card = 3 := hfull
  have hn₄ : hammingDist x.val w.val ≠ 4 := by
    apply no_four_distance_with_all_branches hb x.property I
      (regular_directions C hr x.property) (fun i hi => (mem_directions C x.val i).mp hi)
    intro i hi
    exact paths_in_all_root_directions hr hb x w hout hfull i ((mem_directions C x.val i).mp hi)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
  obtain ⟨hzthird, hzw'⟩ := Finset.mem_filter.mp hz
  have h3 := third_distance hzthird
  have h1 : hammingDist z.val w.val = 1 := hzw'
  have hu := hammingDist_triangle x.val z.val w.val
  have hp := cubeParity_ne_of_adj hzw'
  have hxp : cubeParity x.val ≠ cubeParity z.val := by
    intro he
    have := (distance_parity x.val z.val).mpr he
    omega
  have hsame : cubeParity x.val = cubeParity w.val := by
    cases hx : cubeParity x.val <;> cases hz : cubeParity z.val <;>
      cases hw : cubeParity w.val <;> simp_all
  have hmod := (distance_parity x.val w.val).mpr hsame
  have hzero : hammingDist x.val w.val ≠ 0 := by
    intro he
    have he' : w = x := Subtype.ext ((hammingDist_eq_zero.mp he).symm)
    exact hout (by rw [he']; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _))
  omega

#print axioms full_attachment_distance_two

open private diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self diff_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

private lemma flip_triangle_commute (r : Q 9) (i p q : Fin 9) :
    flip (flip (flip r i) p) q = flip (flip (flip r p) q) i := by
  rw [flip_comm r i p, flip_comm (flip r p) i q]

private lemma diff_three_flips (r : Q 9) {i p q : Fin 9}
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q) :
    diff (flip (flip (flip r i) p) q) r = {q,p,i} := by
  rw [diff_flip, diff_flip, diff_flip, diff_self]
  simp [hip, hiq, hpq, Ne.symm hip, Ne.symm hiq, Ne.symm hpq]

private lemma full_word_last_direction {C : Finset (Q 9)} {r w : Q 9} {i p q : Fin 9}
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hi : flip r i ∈ C)
    (hshort : ¬∃ a ∈ C, (hypercube 9).Adj r a ∧ (hypercube 9).Adj a w)
    (h₂ : hammingDist r w = 2)
    (h : (hypercube 9).Adj (flip (flip (flip r i) p) q) w) :
    flip (flip (flip (flip r i) p) q) i = w := by
  let z := flip (flip (flip r i) p) q
  obtain ⟨k,hk⟩ := adjacent_exists_flip h
  have hdiff : diff z r = {q,p,i} := diff_three_flips r hip hiq hpq
  have hcount : (diff w r).card = 2 := by
    rw [diff_symm w r]
    exact h₂
  have hkD : k ∈ diff z r := by
    by_contra hn
    rw [hk, diff_flip, if_neg hn, Finset.card_insert_of_notMem hn, hdiff] at hcount
    simp [hip, hiq, hpq, Ne.symm hip, Ne.symm hiq, Ne.symm hpq] at hcount
  rw [hdiff] at hkD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkD
  rcases hkD with hq | hp | hi'
  · subst k
    exfalso
    apply hshort
    refine ⟨flip r i, hi, BalancedCriticalSpectrum.flip_adj _ _, ?_⟩
    rw [hk]
    change (hypercube 9).Adj (flip r i) (flip (flip (flip (flip r i) p) q) q)
    rw [BalancedCriticalSpectrum.flip_flip]
    exact BalancedCriticalSpectrum.flip_adj _ _
  · subst k
    exfalso
    apply hshort
    refine ⟨flip r i, hi, BalancedCriticalSpectrum.flip_adj _ _, ?_⟩
    rw [hk]
    change (hypercube 9).Adj (flip r i) (flip (flip (flip (flip r i) p) q) p)
    rw [flip_comm (flip r i) p q, BalancedCriticalSpectrum.flip_flip]
    exact BalancedCriticalSpectrum.flip_adj _ _
  · subst k
    exact hk.symm

private lemma no_selected_initial_of_full_pair {C : Finset (Q 9)}
    (r : Q 9) (p q : Fin 9)
    (hshort : ¬∃ a ∈ C, (hypercube 9).Adj r a ∧
      (hypercube 9).Adj a (flip (flip r p) q)) :
    flip r p ∉ C ∧ flip r q ∉ C := by
  constructor
  · intro hp
    exact hshort ⟨_,hp,BalancedCriticalSpectrum.flip_adj _ _,BalancedCriticalSpectrum.flip_adj _ _⟩
  · intro hq
    apply hshort
    refine ⟨_,hq,BalancedCriticalSpectrum.flip_adj _ _,?_⟩
    rw [flip_comm r p q]
    exact BalancedCriticalSpectrum.flip_adj _ _

#print axioms full_word_last_direction

private lemma diff_two_flips (r : Q 9) {p q : Fin 9} (hpq : p ≠ q) :
    diff (flip (flip r p) q) r = {q,p} := by
  rw [diff_flip, diff_flip, diff_self]
  simp [Ne.symm hpq]

private lemma pair_directions_of_flip_eq (r : Q 9) {p q u v : Fin 9}
    (hpq : p ≠ q) (huv : u ≠ v) (heq : flip (flip r p) q = flip (flip r u) v) :
    (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
  have hsets : ({q,p} : Finset (Fin 9)) = {v,u} := by
    simpa only [diff_two_flips r hpq, diff_two_flips r huv] using congrArg (fun z => diff z r) heq
  have hu : u ∈ ({q,p} : Finset (Fin 9)) := by rw [hsets]; simp
  have hv : v ∈ ({q,p} : Finset (Fin 9)) := by rw [hsets]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (huv (hu.trans hv.symm)).elim
  · exact Or.inr ⟨hu,hv⟩
  · exact Or.inl ⟨hu,hv⟩
  · exact (huv (hu.trans hv.symm)).elim

private lemma full_branches_same_order {C : Finset (Q 9)} {r w : Q 9}
    (hb : IsBalanced C) (hr : r ∈ C)
    (hshort : ¬∃ a ∈ C, (hypercube 9).Adj r a ∧ (hypercube 9).Adj a w)
    (hrank : hammingDist r w = 2)
    {i p q : Fin 9} (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hi : flip r i ∈ C) (hi₂ : flip (flip r i) p ∈ C)
    (hi₃ : flip (flip (flip r i) p) q ∈ C)
    (hiw : (hypercube 9).Adj (flip (flip (flip r i) p) q) w) (hw : w ∈ C)
    {j u v : Fin 9} (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hj : flip r j ∈ C) (hj₂ : flip (flip r j) u ∈ C)
    (hj₃ : flip (flip (flip r j) u) v ∈ C)
    (hjw : (hypercube 9).Adj (flip (flip (flip r j) u) v) w) :
    u = p ∧ v = q := by
  have hei := full_word_last_direction hip hiq hpq hi hshort hrank hiw
  have hej := full_word_last_direction hju hjv huv hj hshort hrank hjw
  have hEnd (a b c : Fin 9) :
      flip (flip (flip (flip r a) b) c) a = flip (flip r b) c := by
    rw [flip_triangle_commute r a b c, BalancedCriticalSpectrum.flip_flip]
  have hpairs := pair_directions_of_flip_eq r hpq huv
    (((hEnd i p q).symm.trans hei).trans ((hEnd j u v).symm.trans hej).symm)
  rcases hpairs with h | ⟨hu,hv⟩
  · exact h
  · subst u
    subst v
    have hin : flip (flip (flip (flip r i) p) q) i ∈ C := hei.symm ▸ hw
    exact (no_oppositely_ordered_middle hb hip hiq hjv hju hpq hr hi hi₂ hi₃ hin
      hj hj₂ hj₃ (hei.trans hej.symm)).elim

#print axioms full_branches_same_order

open private mem_second from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity

private lemma no_two_steps_to_outside {C : Finset (Q 9)} (x w : (C : Set (Q 9)))
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x) :
    ¬∃ a ∈ C, (hypercube 9).Adj x.val a ∧ (hypercube 9).Adj a w.val := by
  rintro ⟨a, ha, hxa, haw⟩
  apply hout
  apply Finset.mem_union_left
  by_cases h : w = x
  · rw [h]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (mem_second.mpr ⟨⟨a,ha⟩,hxa,haw,h⟩)

private lemma full_attachment_same_order {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x w : (C : Set (Q 9)))
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3)
    {i p q : Fin 9}
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hi : flip x.val i ∈ C) (hi₂ : flip (flip x.val i) p ∈ C)
    (hi₃ : flip (flip (flip x.val i) p) q ∈ C)
    (hiw : (hypercube 9).Adj (flip (flip (flip x.val i) p) q) w.val) :
    flip x.val p ∉ C ∧ flip x.val q ∉ C ∧ w.val = flip (flip x.val p) q ∧
      ∀ j : Fin 9, flip x.val j ∈ C →
        flip (flip x.val j) p ∈ C ∧ flip (flip (flip x.val j) p) q ∈ C := by
  have hshort := no_two_steps_to_outside x w hout
  have hrank := full_attachment_distance_two hr hb x w hout hfull
  have he := full_word_last_direction hip hiq hpq hi hshort hrank hiw
  rw [flip_triangle_commute x.val i p q, BalancedCriticalSpectrum.flip_flip] at he
  obtain ⟨hpout,hqout⟩ := no_selected_initial_of_full_pair x.val p q (he.symm ▸ hshort)
  refine ⟨hpout,hqout,he.symm,?_⟩
  intro j hj
  obtain ⟨u,v,hju,huv,hj₂,hj₃,hjw⟩ := paths_in_all_root_directions hr hb x w hout hfull j hj
  have hjv := BalancedCubeGirth.three_directions_distinct hb hju huv x.property hj hj₂ hj₃
  obtain ⟨rfl,rfl⟩ := full_branches_same_order hb x.property hshort hrank
    hip hiq hpq hi hi₂ hi₃ hiw w.property hju hjv huv hj hj₂ hj₃ hjw
  exact ⟨hj₂,hj₃⟩

#print axioms full_attachment_same_order

open private diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

private lemma common_cube_neighbor_unique {C : Finset (Q 9)}
    (hb : IsBalanced C) {z y w a : Q 9}
    (hz : z ∈ C) (hy : y ∈ C) (hw : w ∈ C) (ha : a ∈ C) (hzy : z ≠ y)
    (hzw : (hypercube 9).Adj z w) (hyw : (hypercube 9).Adj y w)
    (hza : (hypercube 9).Adj z a) (hya : (hypercube 9).Adj y a) :
    w = a := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let Z : (C : Set (Q 9)) := ⟨z,hz⟩
  let Y : (C : Set (Q 9)) := ⟨y,hy⟩
  let W : (C : Set (Q 9)) := ⟨w,hw⟩
  let A : (C : Set (Q 9)) := ⟨a,ha⟩
  have hZY : Z ≠ Y := fun he => hzy (congrArg Subtype.val he)
  have hZW : G.Adj Z W := hzw
  have hWY : G.Adj W Y := hyw.symm
  have hZA : G.Adj Z A := hza
  have hAY : G.Adj A Y := hya.symm
  let P : G.Walk Z Y := .cons hZW (.cons hWY .nil)
  let Qw : G.Walk Z Y := .cons hZA (.cons hAY .nil)
  have hp : P.IsPath := by simp [P, Walk.cons_isPath_iff, hZY, hZW.ne, hWY.ne]
  have hq : Qw.IsPath := by simp [Qw, Walk.cons_isPath_iff, hZY, hZA.ne, hAY.ne]
  have he := endpoint_eq_of_short_paths (BalancedCubeGirth.eight_le_egirth C hb)
    hp hq (by simp [P,Qw])
  have he' : W = A := by simpa [P,Qw] using congrArg Walk.support he
  exact congrArg Subtype.val he'

private lemma no_second_leaf_at_covered_leaf {C : Finset (Q 9)} {r : Q 9}
    (hb : IsBalanced C) (hr : r ∈ C)
    {i j p q u v : Fin 9}
    (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hi : flip r i ∈ C) (hj : flip r j ∈ C)
    (hpout : flip r p ∉ C) (hqout : flip r q ∉ C)
    (hi₂ : flip (flip r i) p ∈ C) (hj₂ : flip (flip r j) p ∈ C)
    (hj₃ : flip (flip (flip r j) p) q ∈ C)
    (hy₂ : flip (flip r j) u ∈ C)
    {z y w a : Q 9}
    (hz : z = flip (flip (flip r i) p) q) (hy : y = flip (flip (flip r j) u) v)
    (hw : w = flip (flip r p) q) (hwC : w ∈ C) (ha : a ∈ C)
    (hzC : z ∈ C) (hyC : y ∈ C) (hzy : z ≠ y) (hwa : w ≠ a)
    (hza : (hypercube 9).Adj z a) (hya : (hypercube 9).Adj y a) : False := by
  have hjp : j ≠ p := fun he => hpout (he ▸ hj)
  have hjq : j ≠ q := fun he => hqout (he ▸ hj)
  have hui : u ≠ i := by
    intro he
    subst u
    exact BalancedCubeGirth.no_selected_square hb hij.symm hr hj hi hy₂
  let A : Finset (Fin 9) := {q,p,i}
  let B : Finset (Fin 9) := {v,u,j}
  have hA : A.card = 3 := by simp [A, Finset.card_insert_of_notMem, hip, hiq, hpq,
    Ne.symm hip, Ne.symm hiq, Ne.symm hpq]
  have hB : B.card = 3 := by simp [B, Finset.card_insert_of_notMem, hju, hjv, huv,
    Ne.symm hju, Ne.symm hjv, Ne.symm huv]
  have hcount : 2 ≤ (A ∩ B).card := by
    have hh := diff_triangle_card z y r
    rw [show diff z r = A by rw [hz]; exact diff_three_flips r hip hiq hpq,
      show diff y r = B by rw [hy]; exact diff_three_flips r hju hjv huv, hA, hB] at hh
    have hd : (diff z y).card ≤ 2 :=
      (hammingDist_triangle z a y).trans (show hammingDist z a + hammingDist a y ≤ 2 from
        by rw [show hammingDist z a = 1 from hza, show hammingDist a y = 1 from hya.symm])
    omega
  have hjA : j ∉ A := by simp [A, hij.symm, hjp, hjq]
  have huA : u ∈ A := by
    by_contra h
    have hm : A ∩ B ⊆ {v} := by
      intro k hk
      obtain ⟨hkA,hkB⟩ := Finset.mem_inter.mp hk
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hkB
      rcases hkB with rfl | rfl | rfl
      · simp
      · exact (h hkA).elim
      · exact (hjA hkA).elim
    have hh := Finset.card_le_card hm
    simp at hh
    omega
  have hvA : v ∈ A := by
    by_contra h
    have hm : A ∩ B ⊆ {u} := by
      intro k hk
      obtain ⟨hkA,hkB⟩ := Finset.mem_inter.mp hk
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hkB
      rcases hkB with rfl | rfl | rfl
      · exact (h hkA).elim
      · simp
      · exact (hjA hkA).elim
    have hh := Finset.card_le_card hm
    simp at hh
    omega
  have hzw : (hypercube 9).Adj z w := by
    rw [hw,hz,flip_triangle_commute r i p q]
    exact (BalancedCriticalSpectrum.flip_adj _ _).symm
  have hNo (hyw : (hypercube 9).Adj y w) : False :=
    hwa (common_cube_neighbor_unique hb hzC hyC hwC ha hzy hzw hyw hza hya)
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at huA hvA
  rcases huA with hu | hu | hu
  · subst u
    rcases hvA with hv | hv | hv
    · exact huv hv.symm
    · subst v
      apply hNo
      rw [hw,hy,flip_triangle_commute r j q p,flip_comm r q p]
      exact (BalancedCriticalSpectrum.flip_adj _ _).symm
    · exact BalancedCubeGirth.no_selected_square hb hpq hj hj₂ hy₂ hj₃
  · subst u
    rcases hvA with hv | hv | hv
    · subst v
      apply hNo
      rw [hw,hy,flip_triangle_commute r j p q]
      exact (BalancedCriticalSpectrum.flip_adj _ _).symm
    · exact huv hv.symm
    · subst v
      have he : flip (flip (flip r i) p) j = flip (flip (flip r j) p) i := by
        calc
          _ = flip (flip (flip r i) j) p := flip_comm _ _ _
          _ = flip (flip (flip r j) i) p := by rw [flip_comm r i j]
          _ = _ := flip_comm _ _ _
      exact no_selected_reverse_three hb hip hij hju.symm hr hi hi₂
        (he.symm ▸ (hy ▸ hyC)) hj hy₂ (hy ▸ hyC) he
  · exact hui hu

#print axioms no_second_leaf_at_covered_leaf

open private hamming_two_four_of_blocking from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthNeighborhoodProbe

private lemma word_to_third {C : Finset (Q 9)} (hb : IsBalanced C) (x z : (C : Set (Q 9)))
    (hz : z ∈ third ((hypercube 9).induce (C : Set (Q 9))) x) :
    ∃ i p q : Fin 9, i ≠ p ∧ i ≠ q ∧ p ≠ q ∧
      flip x.val i ∈ C ∧ flip (flip x.val i) p ∈ C ∧
      z.val = flip (flip (flip x.val i) p) q := by
  obtain ⟨a,b,hxa,hab,hbz,hxb,haz,_,_⟩ := third_witness hz
  obtain ⟨i,hi⟩ := adjacent_exists_flip (show (hypercube 9).Adj x.val a.val from hxa)
  obtain ⟨p,hp⟩ := adjacent_exists_flip (show (hypercube 9).Adj a.val b.val from hab)
  obtain ⟨q,hq⟩ := adjacent_exists_flip (show (hypercube 9).Adj b.val z.val from hbz)
  rw [hi] at hp
  rw [hp] at hq
  have hiC : flip x.val i ∈ C := hi ▸ a.property
  have hpC : flip (flip x.val i) p ∈ C := hp ▸ b.property
  have hqC : flip (flip (flip x.val i) p) q ∈ C := hq ▸ z.property
  have hip : i ≠ p := by
    intro he
    subst p
    exact hxb (Subtype.ext (by simpa [BalancedCriticalSpectrum.flip_flip] using hp.symm))
  have hpq : p ≠ q := by
    intro he
    subst q
    apply haz
    apply Subtype.ext
    rw [hi]
    simpa [BalancedCriticalSpectrum.flip_flip] using hq.symm
  exact ⟨i,p,q,hip,BalancedCubeGirth.three_directions_distinct hb hip hpq x.property hiC hpC hqC,
    hpq,hiC,hpC,hq⟩

private lemma distinct_branches_of_common_exterior {C : Finset (Q 9)}
    (hb : IsBalanced C) (x z y a : (C : Set (Q 9))) (hzy : z ≠ y)
    (hout : a ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hzthird : z ∈ third ((hypercube 9).induce (C : Set (Q 9))) x)
    (hythird : y ∈ third ((hypercube 9).induce (C : Set (Q 9))) x)
    {i p q u v : Fin 9}
    (hi : flip x.val i ∈ C) (hp : flip (flip x.val i) p ∈ C)
    (hu : flip (flip x.val i) u ∈ C)
    (hz : z.val = flip (flip (flip x.val i) p) q)
    (hy : y.val = flip (flip (flip x.val i) u) v)
    (hza : (hypercube 9).Adj z.val a.val) (hya : (hypercube 9).Adj y.val a.val) :
    False := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let s : (C : Set (Q 9)) := ⟨flip x.val i,hi⟩
  let b : (C : Set (Q 9)) := ⟨flip s.val p,hp⟩
  let c : (C : Set (Q 9)) := ⟨flip s.val u,hu⟩
  have hsx : G.Adj x s := BalancedCriticalSpectrum.flip_adj _ _
  have hsb : G.Adj s b := BalancedCriticalSpectrum.flip_adj _ _
  have hsc : G.Adj s c := BalancedCriticalSpectrum.flip_adj _ _
  have hbz : G.Adj b z := by
    change (hypercube 9).Adj b.val z.val
    rw [hz]
    exact BalancedCriticalSpectrum.flip_adj _ _
  have hcy : G.Adj c y := by
    change (hypercube 9).Adj c.val y.val
    rw [hy]
    exact BalancedCriticalSpectrum.flip_adj _ _
  have hzo : G.Adj z a := hza
  have hyo : G.Adj y a := hya
  have hsa : s ≠ a := by
    intro he
    apply hout
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ ((G.mem_neighborFinset _ _).mpr hsx))
  have hba : b ≠ a := by
    intro he
    exact no_two_steps_to_outside x a hout ⟨s.val,s.property,hsx,he ▸ hsb⟩
  have hca : c ≠ a := by
    intro he
    exact no_two_steps_to_outside x a hout ⟨s.val,s.property,hsx,he ▸ hsc⟩
  have hsz : s ≠ z := by
    intro he
    have hh := (third_witness hzthird).choose_spec.choose_spec.2.2.2.2.2.2
    exact hh (he ▸ ((G.mem_neighborFinset _ _).mpr hsx))
  have hsy : s ≠ y := by
    intro he
    have hh := (third_witness hythird).choose_spec.choose_spec.2.2.2.2.2.2
    exact hh (he ▸ ((G.mem_neighborFinset _ _).mpr hsx))
  let P : G.Walk s a := .cons hsb (.cons hbz (.cons hzo .nil))
  let Qw : G.Walk s a := .cons hsc (.cons hcy (.cons hyo .nil))
  have hp' : P.IsPath := by simp [P, Walk.cons_isPath_iff, hsb.ne, hbz.ne, hzo.ne, hsz,hsa,hba]
  have hq' : Qw.IsPath := by simp [Qw, Walk.cons_isPath_iff, hsc.ne, hcy.ne, hyo.ne, hsy,hsa,hca]
  have he := endpoint_eq_of_short_paths (BalancedCubeGirth.eight_le_egirth C hb)
    hp' hq' (by simp [P,Qw])
  have hvertices : b = c ∧ z = y := by simpa [P,Qw] using congrArg Walk.support he
  exact hzy hvertices.2

private lemma actual_full_leaf_blocking {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x : (C : Set (Q 9))) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    ∀ z ∈ third G x, ∀ w ∉ HammingSeven.ball G x, ∀ a ∉ HammingSeven.ball G x,
      G.Adj z w → G.Adj z a → w ≠ a →
      ((third G x).filter (fun v => G.Adj v w)).card = 3 →
      ((third G x).filter (fun v => G.Adj v a)).card = 1 := by
  dsimp only
  intro z hz w hw a ha hzw hza hwa hfull
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := (third G x).filter (fun y => G.Adj y a)
  have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hza⟩
  change A.card = 1
  have hpos := Finset.card_pos.mpr ⟨z,hzA⟩
  by_contra hn
  obtain ⟨y,hyA,hyz⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) z
  obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hyA
  obtain ⟨i,p,q,hip,hiq,hpq,hi,hi₂,hzi⟩ := word_to_third hb x z hz
  obtain ⟨j,u,v,hju,hjv,huv,hj,hy₂,hyj⟩ := word_to_third hb x y hy
  have hfullz : (hypercube 9).Adj (flip (flip (flip x.val i) p) q) w.val := by
    rw [← hzi]
    exact hzw
  have hiz : flip (flip (flip x.val i) p) q ∈ C := hzi ▸ z.property
  obtain ⟨hpout,hqout,hwp,hjpath⟩ := full_attachment_same_order hr hb x w hw hfull hip hiq hpq
    hi hi₂ hiz hfullz
  have hij : i ≠ j := by
    intro he
    subst j
    exact distinct_branches_of_common_exterior hb x z y a hyz.symm ha hz hy
      hi hi₂ hy₂ hzi hyj hza hya
  obtain ⟨hj₂,hj₃⟩ := hjpath j hj
  exact no_second_leaf_at_covered_leaf hb x.property hij hip hiq hpq hju hjv huv hi hj hpout hqout
    hi₂ hj₂ hj₃ hy₂ hzi hyj hwp w.property a.property z.property y.property
    (fun h => hyz (Subtype.ext h.symm)) (fun h => hwa (Subtype.ext h)) hza hya

private lemma balanced_cubic_hamming_two_four {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x : (C : Set (Q 9))) :
    18 ≤ (Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = 2)).card +
      (Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = 4)).card :=
  hamming_two_four_of_blocking hr hb x (actual_full_leaf_blocking hr hb x)

#print axioms balanced_cubic_hamming_two_four
