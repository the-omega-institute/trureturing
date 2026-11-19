import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
import Batteries.Tactic.OpenPrivate

/-! The actual normalized embedding carries integer switching values. Their
restriction to the chosen half determines all values across the cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip_adj flip_flip)
open BalancedCubeLowerBound (coordinateSlice)
open Q9EightCubicGraphCertificate (modelAdj)
open private cube_action_regular_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private matrix_true_prefix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private theta theta_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
open private diff diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

attribute [local instance] Classical.propDecidable
local notation "flip" => BalancedCriticalSpectrum.flip

/-- Undirected model edges, represented by their increasing endpoint pair. -/
def modelEdges (wagner : Bool) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ modelAdj wagner e.1 e.2 = true

private theorem constant_on_model (wagner : Bool) (c : Fin 8 → Bool)
    (h : ∀ i j, modelAdj wagner i j = true → c i = c j) : ∀ i, c i = c 0 := by
  have paths : ∀ (w : Bool) (i : Fin 8),
      i = 0 ∨ modelAdj w i 0 = true ∨
      (∃ j, modelAdj w i j = true ∧ modelAdj w j 0 = true) ∨
      ∃ j k, modelAdj w i j = true ∧ modelAdj w j k = true ∧ modelAdj w k 0 = true := by
    decide +kernel
  intro i
  rcases paths wagner i with rfl | h0 | ⟨j, hij, hj0⟩ | ⟨j, k, hij, hjk, hk0⟩
  · rfl
  · exact h _ _ h0
  · exact (h _ _ hij).trans (h _ _ hj0)
  · exact (h _ _ hij).trans ((h _ _ hjk).trans (h _ _ hk0))

/-- The eight embedded vertices and their twelve realized edge middles
exhaust the actual twenty-point half. -/
theorem slice_eq_highs_union_middles (S : Finset (Q 9)) (hS : S.card = 20)
    (wagner : Bool) (p : Fin 8 ↪ Q 9) (hp : ∀ k, p k ∈ S)
    (hm : ∀ i j, modelAdj wagner i j = true → ∃ m ∈ S,
      ∀ k, (hypercube 9).Adj m (p k) ↔ k = i ∨ k = j) :
    ∃ (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9),
      S = Finset.univ.map p ∪ Finset.univ.map m ∧
      ∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2 := by
  classical
  have edges (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      e.val.1 < e.val.2 ∧ modelAdj wagner e.val.1 e.val.2 = true :=
    (Finset.mem_filter.mp e.property).2
  choose mid hmS hmAdj using fun e : (modelEdges wagner : Set (Fin 8 × Fin 8)) =>
    hm e.val.1 e.val.2 (edges e).2
  have hpar : ∀ i, cubeParity (p i) = cubeParity (p 0) := by
    apply constant_on_model wagner
    intro i j hij
    obtain ⟨m, _, hadj⟩ := hm i j hij
    have hbool : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
    exact hbool _ _ _
      (cubeParity_ne_of_adj ((hadj i).mpr (Or.inl rfl)))
      (cubeParity_ne_of_adj ((hadj j).mpr (Or.inr rfl)))
  have hinj : Function.Injective mid := by
    intro e f hef
    have hpair (k : Fin 8) : (k = e.val.1 ∨ k = e.val.2) ↔
        (k = f.val.1 ∨ k = f.val.2) := by
      rw [← hmAdj e k, ← hmAdj f k, hef]
    have he1 := (hpair e.val.1).mp (Or.inl rfl)
    have he2 := (hpair e.val.2).mp (Or.inr rfl)
    have hlt := (edges e).1
    have hlt' := (edges f).1
    apply Subtype.ext
    rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
    · exact (by omega : False).elim
    · exact Prod.ext h1 h2
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  let m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9 := ⟨mid, hinj⟩
  have hsub : Finset.univ.map p ∪ Finset.univ.map m ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hv
      exact hp k
    · obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hv
      exact hmS e
  have hdis : Disjoint (Finset.univ.map p) (Finset.univ.map m) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp hw
    have hn := cubeParity_ne_of_adj ((hmAdj e e.val.1).mpr (Or.inl rfl))
    apply hn
    change mid e = p k at he
    rw [he, hpar k, hpar e.val.1]
  have hedges : (modelEdges wagner).card = 12 := by
    cases wagner <;> decide +kernel
  have hcard : (Finset.univ.map p ∪ Finset.univ.map m).card = 20 := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_map, Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    change 8 + Fintype.card ↥(modelEdges wagner) = 20
    rw [Fintype.card_coe, hedges]
  exact ⟨m, (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hS])).symm, hmAdj⟩

/-- A geometric candidate obtained from an actual support admits signed
integer values for its highs and selected middles, together with all of
the ambient row constraints. -/
theorem exists_signed_candidate {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9) (wagner : Bool) (pattern : Fin 5)
      (p : Fin 8 ↪ Q 9) (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9)
      (z : Q 9 → ℤ),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      (fun i => (cubeBitVec 9).symm (p i)) ∈ Q9SeventyTwoEmbeddingSearch.candidates wagner pattern ∧
      (coordinateSlice C b).image g = Finset.univ.map p ∪ Finset.univ.map m ∧
      (∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2) ∧
      (∀ x ∈ C.image g, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ C.image g, z x = 0) ∧
      (∀ x ∈ C.image g, ∀ i : Fin 9, flip x i ∈ C.image g →
        truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ y, z (flip y 0) =
        3 * z y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i) := by
  obtain ⟨g, σ, wagner, pattern, p, hg, hcut, hhigh, hmem, hmid⟩ :=
    Q9SeventyTwoEmbeddingSearch.exists_member hC hr hb b hs
  have hcard : ((coordinateSlice C b).image g).card = 20 := by
    rw [Finset.card_image_of_injective _ g.injective, hs]
  obtain ⟨m, hslice, hAdj⟩ := slice_eq_highs_union_middles _ hcard wagner p hhigh
    (by
      intro i j hij
      obtain ⟨v, hv, _, hvAdj⟩ := hmid i j hij
      exact ⟨v, hv, hvAdj⟩)
  obtain ⟨hrg, hbg⟩ := cube_action_regular_balanced g σ hg hr hb
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hrg hbg
  refine ⟨g, σ, wagner, pattern, p, m, z, hg, hcut, hmem, hslice, hAdj, hunit, hzero, hsign, ?_⟩
  intro y
  have h := hrow y
  have hz : truePrefixSign y (0 : Fin 9) = 1 := by
    simp [truePrefixSign]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9)), hz, one_mul] at h
  rw [← h, add_sub_cancel_left]

#print axioms exists_signed_candidate

/-- The two orders of distinct flips give opposite products of the
integer edge signs used to select the middle of a compressed edge. -/
theorem opposite_middle_signs (x : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    truePrefixSign x i * truePrefixSign (flip x i) j =
      -(truePrefixSign x j * truePrefixSign (flip x j) i) := by
  have h := congrFun (BalancedCubeGirth.gamma_anticommute hij (fun _ => (1 : ℝ))) x
  simp only [Pi.neg_apply, BalancedCriticalSpectrum.gamma_apply, mul_one] at h
  rw [matrix_true_prefix x i, matrix_true_prefix (flip x i) j,
    matrix_true_prefix x j, matrix_true_prefix (flip x j) i, flip_comm x j i] at h
  have t (u : Q 9) : theta u ^ 2 = 1 := by
    rcases theta_unit u with hu | hu <;> rw [hu] <;> norm_num
  have tn (u : Q 9) : theta u ≠ 0 := by
    rcases theta_unit u with hu | hu <;> rw [hu] <;> norm_num
  have cancel (a b c u v : ℝ) (hb : b ^ 2 = 1) :
      (a * b * u) * (b * c * v) = (a * c) * (u * v) := by
    calc
      _ = b ^ 2 * ((a * c) * (u * v)) := by ring
      _ = _ := by rw [hb, one_mul]
  rw [cancel _ _ _ _ _ (t (flip x i)), cancel _ _ _ _ _ (t (flip x j)),
    ← mul_neg] at h
  have hs := mul_left_cancel₀ (mul_ne_zero (tn x) (tn (flip (flip x i) j))) h
  exact_mod_cast hs

#print axioms opposite_middle_signs

/-- At distinct endpoints, the signed product identifies the first flip
of the length-two path and hence the middle vertex. -/
theorem signed_middle_unique {x y : Q 9} (hxy : x ≠ y) {i j k l : Fin 9}
    (hy : flip (flip x i) j = y) (hy' : flip (flip x k) l = y)
    (hsign : truePrefixSign x i * truePrefixSign (flip x i) j =
      truePrefixSign x k * truePrefixSign (flip x k) l) : i = k := by
  classical
  by_contra hik
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hxy ((flip_flip x i).symm.trans hy)
  have hy_swap : flip (flip x j) i = y := (flip_comm x i j).symm.trans hy
  obtain ⟨hi, hcount⟩ := diff_of_adj_flip hxy i (hy ▸ flip_adj (flip x i) j)
  have hj := (diff_of_adj_flip hxy j (hy_swap ▸ flip_adj (flip x j) i)).1
  have hk := (diff_of_adj_flip hxy k (hy' ▸ flip_adj (flip x k) l)).1
  have hpair : ({i, j} : Finset (Fin 9)) = diff x y := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rcases (by simpa using ha : a = i ∨ a = j) with rfl | rfl
      · exact hi
      · exact hj
    · simp [hij, hcount]
  have hkj : k = j := by
    rw [← hpair] at hk
    exact (by simpa using hk : k = i ∨ k = j).resolve_left (fun h => hik h.symm)
  subst k
  have hli : l = i := by
    by_contra hne
    have he := congrFun (hy'.trans hy_swap.symm) l
    change flip (flip x j) l l = flip (flip x j) i l at he
    rw [BalancedCriticalSpectrum.flip_apply_same,
      show flip (flip x j) i l = (flip x j) l from Function.update_of_ne hne _ _] at he
    have hbool : ∀ a : Bool, Bool.not a ≠ a := by decide
    exact hbool _ he
  subst l
  have hopen := opposite_middle_signs x hij
  have hzero : truePrefixSign x j * truePrefixSign (flip x j) i = 0 := by omega
  have hnonzero (u : Q 9) (a : Fin 9) : truePrefixSign u a ≠ 0 := by
    exact pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0)
  exact (mul_ne_zero (hnonzero x j) (hnonzero (flip x j) i)) hzero

#print axioms signed_middle_unique

/-- The endpoint signs and the two incident edge signs determine both the
location and sign of a middle vertex. -/
private theorem middle_of_signed_path {x y m : Q 9} {z : Q 9 → ℤ}
    (hxm : (hypercube 9).Adj x m) (hmy : (hypercube 9).Adj m y)
    (hx : z x = 1 ∨ z x = -1) (hm : z m = 1 ∨ z m = -1)
    (h : ∀ u (i : Fin 9), (u = x ∧ flip u i = m) ∨ (u = m ∧ flip u i = y) →
      truePrefixSign u i = z u * z (flip u i)) :
    ∃ i j : Fin 9, m = flip x i ∧ y = flip m j ∧
      truePrefixSign x i * truePrefixSign m j = z x * z y ∧
      z m = z x * truePrefixSign x i := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hxm
  obtain ⟨j, hj⟩ := adjacent_exists_flip hmy
  have hs := h x i (Or.inl ⟨rfl, hi.symm⟩)
  have ht := h m j (Or.inr ⟨rfl, hj.symm⟩)
  rw [← hi] at hs
  rw [← hj] at ht
  refine ⟨i, j, hi, hj, ?_, ?_⟩
  · rw [hs, ht]
    rcases hm with hm | hm <;> rw [hm] <;> ring
  · rw [hs]
    rcases hx with hx | hx <;> rw [hx] <;> ring

/-- For a fixed normalized embedding of the eight high vertices, their
signs determine the entire balanced support. -/
theorem support_eq_of_high_signs {U V : Finset (Q 9)} {wagner : Bool}
    (p : Fin 8 ↪ Q 9)
    (m n : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9)
    (z t : Q 9 → ℤ)
    (hU : coordinateSlice U false = Finset.univ.map p ∪ Finset.univ.map m)
    (hV : coordinateSlice V false = Finset.univ.map p ∪ Finset.univ.map n)
    (hm : ∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2)
    (hn : ∀ e k, (hypercube 9).Adj (n e) (p k) ↔ k = e.val.1 ∨ k = e.val.2)
    (hz : ∀ x ∈ U, z x = 1 ∨ z x = -1) (ht : ∀ x ∈ V, t x = 1 ∨ t x = -1)
    (hz0 : ∀ x ∉ U, z x = 0) (ht0 : ∀ x ∉ V, t x = 0)
    (hzSign : ∀ x ∈ U, ∀ i : Fin 9, flip x i ∈ U →
      truePrefixSign x i = z x * z (flip x i))
    (htSign : ∀ x ∈ V, ∀ i : Fin 9, flip x i ∈ V →
      truePrefixSign x i = t x * t (flip x i))
    (hzRow : ∀ x, z (flip x 0) =
      3 * z x - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign x i * z (flip x i))
    (htRow : ∀ x, t (flip x 0) =
      3 * t x - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign x i * t (flip x i))
    (hp : ∀ k, z (p k) = t (p k)) : U = V := by
  classical
  have highMem (k : Fin 8) : p k ∈ Finset.univ.map p :=
    Finset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have inSet {W : Finset (Q 9)}
      {q : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9}
      (hW : coordinateSlice W false = Finset.univ.map p ∪ Finset.univ.map q)
      {x : Q 9} (hx : x ∈ Finset.univ.map p ∪ Finset.univ.map q) : x ∈ W :=
    (Finset.mem_filter.mp (hW.symm ▸ hx)).1
  have signedPath {W : Finset (Q 9)} {s : Q 9 → ℤ} {x y v : Q 9}
      (hs : ∀ a ∈ W, s a = 1 ∨ s a = -1)
      (hsSign : ∀ a ∈ W, ∀ i : Fin 9, flip a i ∈ W →
        truePrefixSign a i = s a * s (flip a i))
      (hx : x ∈ W) (hy : y ∈ W) (hv : v ∈ W)
      (hxv : (hypercube 9).Adj x v) (hvy : (hypercube 9).Adj v y) :
      ∃ i j : Fin 9, v = flip x i ∧ y = flip v j ∧
        truePrefixSign x i * truePrefixSign v j = s x * s y ∧
        s v = s x * truePrefixSign x i := by
    apply middle_of_signed_path hxv hvy (hs _ hx) (hs _ hv)
    rintro a i (⟨rfl, hflip⟩ | ⟨rfl, hflip⟩)
    · exact hsSign _ hx _ (hflip.symm ▸ hv)
    · exact hsSign _ hv _ (hflip.symm ▸ hy)
  have hmid (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      m e = n e ∧ z (m e) = t (n e) := by
    have hend : p e.val.1 ≠ p e.val.2 := fun he =>
      (Finset.mem_filter.mp e.property).2.1.ne (p.injective he)
    obtain ⟨i, j, hi, hj, hij, hzi⟩ := signedPath hz hzSign
      (inSet hU (Finset.mem_union_left _ (highMem e.val.1)))
      (inSet hU (Finset.mem_union_left _ (highMem e.val.2)))
      (inSet hU (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)))
      ((hm e e.val.1).mpr (Or.inl rfl)).symm ((hm e e.val.2).mpr (Or.inr rfl))
    obtain ⟨k, l, hk, hl, hkl, htk⟩ := signedPath ht htSign
      (inSet hV (Finset.mem_union_left _ (highMem e.val.1)))
      (inSet hV (Finset.mem_union_left _ (highMem e.val.2)))
      (inSet hV (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)))
      ((hn e e.val.1).mpr (Or.inl rfl)).symm ((hn e e.val.2).mpr (Or.inr rfl))
    have hik := signed_middle_unique hend ((congrArg (fun x => flip x j) hi).symm.trans hj.symm)
      ((congrArg (fun x => flip x l) hk).symm.trans hl.symm) (by
        rw [← hi, ← hk, hij, hkl, hp, hp])
    exact ⟨hi.trans (hik ▸ hk.symm), by rw [hzi, htk, hp, hik]⟩
  have hmn : m = n := Function.Embedding.ext fun e => (hmid e).1
  have hhalf (x : Q 9) (hx : x 0 = false) : z x = t x := by
    have hu : x ∈ U ↔ x ∈ coordinateSlice U false := by simp [coordinateSlice, hx]
    have hv : x ∈ V ↔ x ∈ coordinateSlice V false := by simp [coordinateSlice, hx]
    by_cases hxU : x ∈ U
    · have hmemb := hu.mp hxU
      rw [hU] at hmemb
      rcases Finset.mem_union.mp hmemb with hh | hh
      · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hh
        exact hp k
      · obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hh
        exact (hmid e).2.trans (congrArg t (hmid e).1.symm)
    · have hxV : x ∉ V := by
        intro hxV
        apply hxU
        apply hu.mpr
        rw [hU, hmn, ← hV]
        exact hv.mp hxV
      rw [hz0 _ hxU, ht0 _ hxV]
  have hall (x : Q 9) : z x = t x := by
    cases hbit : x 0
    · exact hhalf x hbit
    · let y := flip x 0
      have hy : y 0 = false := by simp [y, hbit]
      have hyx : flip y 0 = x := flip_flip x 0
      rw [← hyx, hzRow, htRow, hhalf y hy]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hhalf (flip y i)]
      exact (Function.update_of_ne (Finset.mem_erase.mp hi).1.symm _ _).trans hy
  have mem_iff_ne_zero (W : Finset (Q 9)) (s : Q 9 → ℤ)
      (hs : ∀ x ∈ W, s x = 1 ∨ s x = -1) (hs0 : ∀ x ∉ W, s x = 0) (x : Q 9) :
      x ∈ W ↔ s x ≠ 0 := by
    constructor
    · intro h
      rcases hs x h with h' | h' <;> simp [h']
    · intro h
      by_contra hn
      exact h (hs0 x hn)
  ext x
  rw [mem_iff_ne_zero U z hz hz0, mem_iff_ne_zero V t ht ht0, hall]

#print axioms support_eq_of_high_signs

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
