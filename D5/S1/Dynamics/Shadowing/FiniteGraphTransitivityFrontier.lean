/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite closure differences and exceptional sets for affine graph dynamics. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphSmallArcs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
Three missing closure points on one edge would trap a preconnected set between
the outer two points. The middle point then separates the set in the edge coordinate.
-/

open Set Function

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

private theorem coord_edgeChart_right {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) :
    coord G (edgeChart G h t) v = t :=
  edgeVector_right h.ne t

private theorem isOpen_edgeChart_image_Ioo {u v : V} (h : G.Adj u v)
    (a b : Icc (0 : ℝ) 1) : IsOpen (edgeChart G h '' Ioo a b) := by
  have heq : edgeChart G h '' Ioo a b =
      {x | 0 < coord G x u} ∩ (fun x => coord G x v) ⁻¹' Ioo (a : ℝ) (b : ℝ) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      change 0 < coord G (edgeChart G h t) u ∧ coord G (edgeChart G h t) v ∈ Ioo (a : ℝ) b
      rw [coord_edgeChart_right, coord_edgeChart, edgeVector_left h.ne]
      have htb : (t : ℝ) < (b : ℝ) := ht.2
      exact ⟨sub_pos.mpr (htb.trans_le b.2.2), ⟨ht.1, ht.2⟩⟩
    · rintro ⟨hu, hv⟩
      obtain ⟨_, t, rfl⟩ := exists_edgeChart_of_two_pos G h.ne hu (a.2.1.trans_lt hv.1)
      rw [mem_preimage, coord_edgeChart_right G h] at hv
      exact ⟨t, ⟨hv.1, hv.2⟩, rfl⟩
  rw [heq]
  exact (isOpen_lt continuous_const (continuous_coord G u)).inter
    (isOpen_Ioo.preimage (continuous_coord G v))

private theorem closure_diff_edgeChart_no_three {u v : V} (h : G.Adj u v)
    {C : Set (Space G)} (hC : IsPreconnected C) {a b c : Icc (0 : ℝ) 1}
    (hab : a < b) (hbc : b < c) (ha : edgeChart G h a ∈ closure C \ C)
    (hb : edgeChart G h b ∈ closure C \ C) (hc : edgeChart G h c ∈ closure C \ C) : False := by
  let U := edgeChart G h '' Ioo a c
  have hU : IsOpen U := isOpen_edgeChart_image_Ioo G h a c
  have hmeet : (C ∩ U).Nonempty := by
    rw [inter_comm]
    exact mem_closure_iff.mp hb.1 _ hU ⟨b, ⟨hab, hbc⟩, rfl⟩
  have hclosed : IsClosed (edgeChart G h '' Icc a c) :=
    (isCompact_Icc.image (continuous_edgeChart G h)).isClosed
  have hinside : C ⊆ U := hC.subset_of_closure_inter_subset hU hmeet (by
    rintro x ⟨hx, hxC⟩
    obtain ⟨t, ht, rfl⟩ := closure_minimal (image_mono Ioo_subset_Icc_self) hclosed hx
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
    · rintro rfl
      exact ha.2 hxC
    · rintro rfl
      exact hc.2 hxC)
  have havoid : ∀ x ∈ C, coord G x v ≠ (b : ℝ) := by
    intro x hx heq
    obtain ⟨t, _, rfl⟩ := hinside hx
    rw [coord_edgeChart_right G h] at heq
    obtain rfl : t = b := Subtype.ext heq
    exact hb.2 hx
  have hcoord := continuous_coord G v
  rcases hC.mapsTo_Ioi_or_Iio hcoord.continuousOn havoid with habove | hbelow
  · have hbound : closure C ⊆ (fun x => coord G x v) ⁻¹' Ici (b : ℝ) :=
      closure_minimal (fun x hx => (show (b : ℝ) < coord G x v from habove hx).le)
        (isClosed_Ici.preimage hcoord)
    have hle : (b : ℝ) ≤ coord G (edgeChart G h a) v := hbound ha.1
    rw [coord_edgeChart_right G h] at hle
    exact (not_lt_of_ge hle) hab
  · have hbound : closure C ⊆ (fun x => coord G x v) ⁻¹' Iic (b : ℝ) :=
      closure_minimal (fun x hx => (show coord G x v < (b : ℝ) from hbelow hx).le)
        (isClosed_Iic.preimage hcoord)
    have hle : coord G (edgeChart G h c) v ≤ (b : ℝ) := hbound hc.1
    rw [coord_edgeChart_right G h] at hle
    exact (not_lt_of_ge hle) hbc

private theorem finite_closure_diff_edgeChart {u v : V} (h : G.Adj u v)
    {C : Set (Space G)} (hC : IsPreconnected C) :
    (edgeChart G h ⁻¹' (closure C \ C)).Finite := by
  classical
  let T := edgeChart G h ⁻¹' (closure C \ C)
  change T.Finite
  by_cases hT : T.Subsingleton
  · exact hT.finite
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a ∈ T ∧ b ∈ T ∧ a < b := by
    obtain ⟨s, hs, t, ht, hst⟩ := not_subsingleton_iff.mp hT
    rcases lt_or_gt_of_ne hst with hlt | hlt
    · exact ⟨s, t, hs, ht, hlt⟩
    · exact ⟨t, s, ht, hs, hlt⟩
  refine (finite_singleton b |>.insert a).subset (subset_pair_iff.mpr ?_)
  intro t ht
  rcases lt_trichotomy t a with hta | rfl | hat
  · exact (closure_diff_edgeChart_no_three G h hC hta hab ht ha hb).elim
  · exact Or.inl rfl
  rcases lt_trichotomy t b with htb | rfl | hbt
  · exact (closure_diff_edgeChart_no_three G h hC hat htb ha ht hb).elim
  · exact Or.inr rfl
  · exact (closure_diff_edgeChart_no_three G h hC hab hbt ha hb ht).elim

/-- The closure of a preconnected subset of an affine finite graph adds only
finitely many points. -/
theorem finite_closure_diff_of_isPreconnected [Finite V] {C : Set (Space G)}
    (hC : IsPreconnected C) : (closure C \ C).Finite := by
  let E := {e : V × V // G.Adj e.1 e.2}
  let extra (e : E) := edgeChart G e.2 '' (edgeChart G e.2 ⁻¹' (closure C \ C))
  have hfinite : (range (vertex G) ∪ ⋃ e : E, extra e).Finite :=
    (finite_range _).union (finite_iUnion fun e =>
      (finite_closure_diff_edgeChart G e.2 hC).image _)
  refine hfinite.subset ?_
  intro x hx
  rcases x.property with ⟨u, hu⟩ | he
  · exact Or.inl ⟨u, Subtype.ext hu⟩
  · obtain ⟨e, t, ht⟩ := mem_iUnion.mp he
    have heq : edgeChart G e.2 t = x := Subtype.ext ht
    exact Or.inr (mem_iUnion_of_mem e ⟨t, by rw [mem_preimage, heq]; exact hx, heq⟩)

private theorem finite_compl_iUnion_iterate_image_of_return [Finite V]
    {f : Space G → Space G} (hf : Continuous f) {J : Set (Space G)}
    (hJ : IsPreconnected J) (hdense : Dense (⋃ n : ℕ, f^[n] '' J))
    {k : ℕ} (hk : 0 < k) (hreturn : (f^[k] '' J ∩ J).Nonempty) :
    ((⋃ n : ℕ, f^[n] '' J)ᶜ).Finite := by
  obtain ⟨y, ⟨x, hxJ, hxy⟩, hyJ⟩ := hreturn
  let C (i : Fin k) := ⋃ m : ℕ, f^[k * m + (i : ℕ)] '' J
  have hC (i : Fin k) : IsPreconnected (C i) := by
    apply IsPreconnected.iUnion_of_chain
    · exact fun m => hJ.image _ (hf.iterate (k * m + i)).continuousOn
    · intro m
      refine ⟨f^[k * m + (i : ℕ)] y, ⟨y, hyJ, rfl⟩, x, hxJ, ?_⟩
      change f^[k * (m + 1) + (i : ℕ)] x = _
      rw [Nat.mul_succ, show k * m + k + (i : ℕ) = k * m + (i : ℕ) + k by ac_rfl,
        iterate_add_apply, hxy]
  have hcover : (⋃ i, C i) = ⋃ n : ℕ, f^[n] '' J := by
    ext z
    simp only [C, mem_iUnion]
    constructor
    · rintro ⟨i, m, hm⟩
      exact ⟨k * m + (i : ℕ), hm⟩
    · rintro ⟨n, hn⟩
      refine ⟨⟨n % k, Nat.mod_lt n hk⟩, n / k, ?_⟩
      change z ∈ f^[k * (n / k) + n % k] '' J
      rwa [Nat.add_comm, Nat.mod_add_div]
  have hclosure : closure (⋃ n : ℕ, f^[n] '' J) = ⋃ i, closure (C i) := by
    rw [← hcover, closure_iUnion_of_finite]
  refine (finite_iUnion fun i => finite_closure_diff_of_isPreconnected G (hC i)).subset ?_
  intro z hz
  have hzcl : z ∈ ⋃ i, closure (C i) := hclosure ▸ hdense z
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzcl
  exact mem_iUnion_of_mem i ⟨hi, fun h => hz (hcover ▸ mem_iUnion_of_mem i h)⟩

private theorem exists_edgeChart_Icc_subset [Nontrivial V] (hG : G.Connected)
    {U : Set (Space G)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (u v : V) (h : G.Adj u v) (a b : Icc (0 : ℝ) 1),
      0 < (a : ℝ) ∧ a < b ∧ (b : ℝ) < 1 ∧ edgeChart G h '' Icc a b ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  let s₀ : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  let s₁ : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  obtain ⟨u, v, h, t, rfl⟩ :
      ∃ (u v : V) (h : G.Adj u v) (t : Icc (0 : ℝ) 1), x = edgeChart G h t := by
    rcases x.property with ⟨u, hu⟩ | he
    · obtain ⟨v, h⟩ := hG.preconnected.exists_adj_of_nontrivial u
      exact ⟨u, v, h, s₀, (Subtype.ext hu.symm).trans (edgeChart_zero G h).symm⟩
    · obtain ⟨⟨⟨u, v⟩, h⟩, t, ht⟩ := mem_iUnion.mp he
      exact ⟨u, v, h, t, Subtype.ext ht.symm⟩
  have h01 : s₀ < s₁ := zero_lt_one
  have htcl : t ∈ closure (Ioo s₀ s₁) := by
    rw [closure_Ioo h01.ne]
    exact t.2
  have hpre := hU.preimage (continuous_edgeChart G h)
  have hW : ((edgeChart G h ⁻¹' U) ∩ Ioo s₀ s₁).Nonempty :=
    mem_closure_iff.mp htcl _ hpre hx
  obtain ⟨l, r, hlr, hsub⟩ := (hpre.inter isOpen_Ioo).exists_Ioo_subset hW
  obtain ⟨b, hlb, hbr⟩ := exists_between hlr
  obtain ⟨a, hla, hab⟩ := exists_between hlb
  refine ⟨u, v, h, a, b, (hsub ⟨hla, hab.trans hbr⟩).2.1, hab,
    (hsub ⟨hlb, hbr⟩).2.2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (hsub ⟨hla.trans_le ht.1, ht.2.trans_lt hbr⟩).1

/-- For a transitive map of a nontrivial connected affine finite graph, each nonempty
open set contains a free closed subarc whose forward images miss only finitely many points.
The map permutes the missed points, and every preimage of a missed point is missed. -/
theorem exists_edgeChart_Icc_finite_exceptional_set [Finite V] [Nontrivial V]
    (hG : G.Connected) {f : Space G → Space G} (hf : Continuous f)
    (htrans : ∀ A B : Set (Space G), IsOpen A → A.Nonempty → IsOpen B → B.Nonempty →
      ∃ n : ℕ, (f^[n] '' A ∩ B).Nonempty)
    {U : Set (Space G)} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (u v : V) (h : G.Adj u v) (a b : Icc (0 : ℝ) 1),
      0 < (a : ℝ) ∧ a < b ∧ (b : ℝ) < 1 ∧ edgeChart G h '' Icc a b ⊆ U ∧
      let E := (⋃ n : ℕ, f^[n] '' (edgeChart G h '' Icc a b))ᶜ
      E.Finite ∧ f ⁻¹' E = E ∧ BijOn f E E := by
  obtain ⟨u, v, h, a, b, ha, hab, hb, hsub⟩ := exists_edgeChart_Icc_subset G hG hU hUne
  refine ⟨u, v, h, a, b, ha, hab, hb, hsub, ?_⟩
  let J := edgeChart G h '' Icc a b
  let O := ⋃ n : ℕ, f^[n] '' J
  let E := Oᶜ
  change E.Finite ∧ f ⁻¹' E = E ∧ BijOn f E E
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  let A := edgeChart G h '' Ioo a m
  let B := edgeChart G h '' Ioo m b
  have hA : IsOpen A := isOpen_edgeChart_image_Ioo G h a m
  have hB : IsOpen B := isOpen_edgeChart_image_Ioo G h m b
  have hAne : A.Nonempty := (nonempty_Ioo.mpr ham).image _
  have hBne : B.Nonempty := (nonempty_Ioo.mpr hmb).image _
  have hAJ : A ⊆ J := image_mono fun _ ht => ⟨ht.1.le, ht.2.le.trans hmb.le⟩
  have hBJ : B ⊆ J := image_mono fun _ ht => ⟨ham.le.trans ht.1.le, ht.2.le⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    have htEq := congrArg (fun x => coord G x v) heq
    simp only [coord_edgeChart_right G h] at htEq
    obtain rfl : t = s := Subtype.ext htEq
    exact (not_lt_of_ge hs.2.le) ht.1
  obtain ⟨k, hk⟩ := htrans A B hA hAne hB hBne
  have hkpos : 0 < k := by
    by_contra hnonpos
    have hzero : k = 0 := by omega
    subst k
    obtain ⟨z, hzA, hzB⟩ := hk
    exact Set.disjoint_left.mp hdisj (by simpa using hzA) hzB
  have hreturn : (f^[k] '' J ∩ J).Nonempty :=
    hk.mono (inter_subset_inter (image_mono hAJ) hBJ)
  have hdense : Dense O := by
    refine dense_iff_inter_open.mpr fun W hW hWne => ?_
    obtain ⟨n, z, hzA, hzW⟩ := htrans A W hA hAne hW hWne
    exact ⟨z, hzW, mem_iUnion_of_mem n (image_mono hAJ hzA)⟩
  have hfin : E.Finite := finite_compl_iUnion_iterate_image_of_return G hf
    (isPreconnected_Icc.image _ (continuous_edgeChart G h).continuousOn) hdense hkpos hreturn
  have hforward : MapsTo f O O := by
    intro z hz
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.mp hz
    exact mem_iUnion_of_mem (n + 1) ⟨x, hx, iterate_succ_apply' f n x⟩
  have hsubE : f ⁻¹' E ⊆ E := fun _ hz hzo => hz (hforward hzo)
  have hsurj : Surjective f := by
    intro y
    by_contra hy
    have hyR : y ∈ (range f)ᶜ := hy
    let z := edgeChart G h a
    have hney : f z ≠ y := fun heq => hy ⟨z, heq⟩
    obtain ⟨P, Q, hP, hQ, hzP, hyQ, hPQ⟩ := t2_separation hney
    have hQ' : IsOpen (Q ∩ (range f)ᶜ) :=
      hQ.inter (isCompact_range hf).isClosed.isOpen_compl
    obtain ⟨n, _, ⟨w, hw, rfl⟩, hhit⟩ :=
      htrans P _ hP ⟨f z, hzP⟩ hQ' ⟨y, hyQ, hyR⟩
    cases n with
    | zero => exact Set.disjoint_left.mp hPQ hw hhit.1
    | succ n => exact hhit.2 ⟨f^[n] w, (iterate_succ_apply' f n w).symm⟩
  have hsurjE : SurjOn f (f ⁻¹' E) E := hsurj.surjOn_preimage
  have heq : f ⁻¹' E = E := hfin.eq_of_subset_of_encard_le' hsubE
    ((encard_le_encard hsurjE).trans (encard_image_le _ _))
  have hmapsE : MapsTo f E E := fun _ hx => heq.symm.subset hx
  have hontoE : SurjOn f E E := hsurjE.trans (image_mono heq.subset)
  exact ⟨hfin, heq, (hfin.surjOn_iff_bijOn_of_mapsTo hmapsE).mp hontoE⟩

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
