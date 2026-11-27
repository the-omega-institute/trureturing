/- GID: D5/S3/Combinatorics/Matroids/CircuitReplacementSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitReplacementSupport
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: One changed basis vector gives disjoint alternating coefficient supports. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

/-! Disjoint coordinate supports after one coordinate replacement. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitReplacementSupport

open Finset

variable {I : Type*} [DecidableEq I]

def oldCoordinateSupport (x : I) (F : Finset I) : Set (Finset I) :=
  {G | G = F ∨ x ∈ F ∧ x ∉ G ∧ F.erase x ⊆ G ∧ G.card = F.card}

private theorem erase_inter (x : I) (F U : Finset I) :
    F.erase x ∩ U.erase x = (F ∩ U).erase x := by
  ext i
  simp only [mem_inter, mem_erase]
  tauto

theorem disjoint_old_coordinate_support (x : I) {F U : Finset I}
    (hsize : F.card = U.card) (hinter : (F ∩ U).card + 2 ≤ F.card) :
    Disjoint (oldCoordinateSupport x F) (oldCoordinateSupport x U) := by
  apply Set.disjoint_left.mpr
  intro G hG hG'
  change G = F ∨ x ∈ F ∧ x ∉ G ∧ F.erase x ⊆ G ∧ G.card = F.card at hG
  change G = U ∨ x ∈ U ∧ x ∉ G ∧ U.erase x ⊆ G ∧ G.card = U.card at hG'
  rcases hG with hEq | ⟨hxF, hxG, hFG, hcard⟩
  · subst G
    rcases hG' with hEq | ⟨hxU, _, hUF, _⟩
    · subst U
      rw [inter_self] at hinter
      omega
    · have hsub : U.erase x ⊆ F ∩ U := subset_inter hUF (erase_subset _ _)
      have hle := card_le_card hsub
      rw [card_erase_of_mem hxU] at hle
      omega
  · rcases hG' with hEq | ⟨hxU, _, hUG, _⟩
    · subst G
      have hsub : F.erase x ⊆ F ∩ U := subset_inter (erase_subset _ _) hFG
      have hle := card_le_card hsub
      rw [card_erase_of_mem hxF] at hle
      omega
    · have hxInter : x ∈ F ∩ U := mem_inter.mpr ⟨hxF, hxU⟩
      have hle := card_le_card (union_subset hFG hUG)
      have hcount := card_union_add_card_inter (F.erase x) (U.erase x)
      rw [erase_inter, card_erase_of_mem hxInter,
        card_erase_of_mem hxF, card_erase_of_mem hxU] at hcount
      have hpos := card_pos.mpr ⟨x, hxInter⟩
      omega


open D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
open Set.powersetCard

private theorem tuple_zero_of_coordinate_zero {M N : Type*} [LinearOrder I]
    [AddCommGroup M] [AddCommGroup N] {k : ℕ}
    (b : Module.Basis I ℤ M) (f : M [⋀^Fin k]→ₗ[ℤ] N)
    (g : Fin k → I) (S : Set.powersetCard I k)
    (hmem : ∀ j, g j ∈ S.val) (hzero : (basisFormEquiv b).symm f S = 0) :
    f (b ∘ g) = 0 := by
  by_cases hinj : Function.Injective g
  · let g' (i : Fin k) : S.val := ⟨g i, hmem i⟩
    have hg' : Function.Bijective g' := by
      apply (Fintype.bijective_iff_injective_and_card _).mpr
      refine ⟨fun i j h => hinj (congrArg Subtype.val h), ?_⟩
      simpa using S.prop.symm
    let gEquiv := Equiv.ofBijective g' hg'
    let sorted := (S.val.orderIsoOfFin S.prop).toEquiv
    let perm := gEquiv.trans sorted.symm
    have hperm (i : Fin k) : (ofFinEmbEquiv.symm S) (perm i) = g i := by
      change ((sorted (sorted.symm (gEquiv i)) : S.val) : I) = g i
      rw [Equiv.apply_symm_apply]
      rfl
    have htuple : b ∘ g = (b ∘ ofFinEmbEquiv.symm S) ∘ perm := by
      funext i
      exact congrArg b (hperm i).symm
    rw [htuple, f.map_perm]
    rw [basisFormEquiv_symm_apply] at hzero
    simp [hzero]
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    exact f.map_eq_zero_of_eq _ (congrArg b hij) hne

theorem old_coordinate_zero_of_replacement_support {M N : Type*}
    [Fintype I] [LinearOrder I] [AddCommGroup M] [AddCommGroup N] {k : ℕ}
    (b c : Module.Basis I ℤ M) (x : I) (hchange : ∀ i ≠ x, c i = b i)
    (f : M [⋀^Fin k]→ₗ[ℤ] N) (F : Set.powersetCard I k)
    (hzero : ∀ G : Set.powersetCard I k, G.val ∈ oldCoordinateSupport x F.val →
      (basisFormEquiv c).symm f G = 0) :
    (basisFormEquiv b).symm f F = 0 := by
  classical
  let e := ofFinEmbEquiv.symm F
  have he (i : Fin k) : e i ∈ F.val :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem F (e i)).mp ⟨i, rfl⟩
  rw [basisFormEquiv_symm_apply]
  change f (b ∘ e) = 0
  by_cases hx : x ∈ F.val
  · obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem F x).mpr hx
    change e j = x at hj
    have htuple : b ∘ e = Function.update (c ∘ e) j (b x) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [hj]
      · have hix : e i ≠ x := fun hh => hi (e.injective (hh.trans hj.symm))
        simp [Function.update_of_ne hi, hchange _ hix]
    rw [htuple, ← c.sum_equivFun (b x), f.map_update_sum]
    apply sum_eq_zero
    intro y _
    rw [f.map_update_smul]
    suffices hyzero : f (Function.update (c ∘ e) j (c y)) = 0 by rw [hyzero, smul_zero]
    by_cases hyx : y = x
    · subst y
      have hup : Function.update (c ∘ e) j (c x) = c ∘ e := by
        rw [← hj]; exact Function.update_eq_self _ _
      rw [hup]
      simpa [basisFormEquiv_symm_apply, e] using hzero F (Or.inl rfl)
    · by_cases hy : y ∈ F.val
      · obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem F y).mpr hy
        change e i = y at hi
        have hij : i ≠ j := fun h => hyx (hi.symm.trans (h ▸ hj))
        apply f.map_eq_zero_of_eq _ (i := i) (j := j) _ hij
        simp [Function.update_of_ne hij, hi]
      · let G : Set.powersetCard I k := ⟨insert y (F.val.erase x), by
          change (insert y (F.val.erase x)).card = k
          rw [card_insert_of_notMem (fun h => hy (mem_of_mem_erase h)), card_erase_of_mem hx]
          have hpos : 0 < F.val.card := card_pos.mpr ⟨x, hx⟩
          have hc : F.val.card = k := F.prop
          omega⟩
        have hg (i : Fin k) : Function.update e j y i ∈ G.val := by
          by_cases hi : i = j
          · subst i
            simp [G]
          · have hix : e i ≠ x := fun hh => hi (e.injective (hh.trans hj.symm))
            rw [Function.update_of_ne hi]
            exact mem_insert_of_mem (mem_erase.mpr ⟨hix, he i⟩)
        have hs : G.val ∈ oldCoordinateSupport x F.val := Or.inr
          ⟨hx, by simp [G, Ne.symm hyx], subset_insert _ _, G.prop.trans F.prop.symm⟩
        have hupdate : Function.update (c ∘ e) j (c y) = c ∘ Function.update e j y := by
          funext i
          by_cases hi : i = j <;> simp [Function.update, Function.comp_def, hi]
        rw [hupdate]
        exact tuple_zero_of_coordinate_zero c f _ G hg (hzero G hs)
  · have htuple : b ∘ e = c ∘ e := by
      funext i
      exact (hchange _ (fun h => hx (h ▸ he i))).symm
    rw [htuple]
    simpa [basisFormEquiv_symm_apply, e] using hzero F (Or.inl rfl)



end D5.S3.Combinatorics.Matroids.CircuitReplacementSupport
