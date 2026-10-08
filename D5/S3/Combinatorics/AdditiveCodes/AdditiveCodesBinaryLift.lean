/- GID: D5/S3/Combinatorics/AdditiveCodes/AdditiveCodesBinaryLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/AdditiveCodesBinaryLift
   mirror-E: none(waiver:binary-product-lift)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Projectivization.Cardinality]
   utility: none
   digest: Product tilings lift the binary seed to blocking sets with separating labels. -/

import D5.S3.Combinatorics.AdditiveCodes.AdditiveCodesBinarySeed
import Mathlib.LinearAlgebra.Projectivization.Cardinality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 1000

namespace D5.S3.Combinatorics.AdditiveCodes

/-- A product lift of the seed provides a blocking direction set and nonlinear labels. -/
theorem binaryLift (a b : ℕ) :
    let V := (Fin 6 → ZMod 2) × (Fin a → ZMod 2) × (Fin b → ZMod 2)
    ∃ B : Finset (Projectivization (ZMod 2) V),
      1 < B.card ∧ (∃ P, P ∉ B) ∧
      (∀ K : Submodule (ZMod 2) V, Module.finrank (ZMod 2) K = a + 3 →
        ∃ P ∈ B, P.submodule ≤ K) ∧
      ∃ label : V → (Fin 3 → ZMod 2) × (Fin b → ZMod 2),
        ∀ x y (hxy : x ≠ y), label x = label y →
          Projectivization.mk (ZMod 2) (x - y) (sub_ne_zero.mpr hxy) ∉ B := by
  dsimp only
  let V := (Fin 6 → ZMod 2) × (Fin a → ZMod 2) × (Fin b → ZMod 2)
  have unique : ∀ v : Fin 6 → ZMod 2,
      ∃! h : Fin 3 → ZMod 2, v - binarySeedShift h ∈ binarySeedPoints := by
    unfold ExistsUnique
    decide
  classical
  letI : Fintype (Projectivization (ZMod 2) V) := Fintype.ofFinite _
  let tile : (Fin 6 → ZMod 2) → (Fin 3 → ZMod 2) :=
    fun v => (unique v).choose
  have htile : ∀ v, v - binarySeedShift (tile v) ∈ binarySeedPoints :=
    fun v => (unique v).choose_spec.1
  have rep_mk : ∀ (v : V) (hv : v ≠ 0),
      (Projectivization.mk (ZMod 2) v hv).rep = v := by
    intro v hv
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod 2) v hv
    have hc1 : (c : ZMod 2) = 1 := by
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h01 c with h | h
      · exact False.elim (c.ne_zero h)
      · exact h
    simpa [Units.smul_def, hc1] using hc.symm
  let B : Finset (Projectivization (ZMod 2) V) :=
    Finset.univ.filter (fun P => P.rep.1 ∉ binarySeedDifferences ∨ P.rep.2.2 ≠ 0)
  have Bmem : ∀ (v : V) (hv : v ≠ 0),
      Projectivization.mk (ZMod 2) v hv ∈ B ↔
        v.1 ∉ binarySeedDifferences ∨ v.2.2 ≠ 0 := by
    intro v hv; simp [B, rep_mk]
  have nozero : (0 : Fin 6 → ZMod 2) ∈ binarySeedDifferences := by decide
  have block : ∀ K : Submodule (ZMod 2) V, Module.finrank (ZMod 2) K = a + 3 →
      ∃ P ∈ B, P.submodule ≤ K := by
    intro K hK
    by_contra h
    have hcontain : ∀ v ∈ K, v.1 ∈ binarySeedDifferences ∧ v.2.2 = 0 := by
      intro v hv
      by_cases hz : v = 0
      · subst v; exact ⟨nozero, rfl⟩
      · by_contra hd
        have hm : Projectivization.mk (ZMod 2) v hz ∈ B :=
          (Bmem v hz).2 (by
            by_cases hm : v.1 ∈ binarySeedDifferences
            · exact Or.inr (fun hz => hd ⟨hm, hz⟩)
            · exact Or.inl hm)
        apply h
        refine ⟨Projectivization.mk (ZMod 2) v hz, hm, ?_⟩
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem v K).mpr hv
    let first : K →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
      (LinearMap.fst (ZMod 2) (Fin 6 → ZMod 2)
        ((Fin a → ZMod 2) × (Fin b → ZMod 2))).comp K.subtype
    have hfirst : ∀ v ∈ first.range, v ∈ binarySeedDifferences := by
      rintro v ⟨w, rfl⟩; exact (hcontain w w.property).1
    have hsmall := binarySeedObstruction first.range hfirst
    let middle : first.ker →ₗ[ZMod 2] (Fin a → ZMod 2) :=
      { toFun := fun w => (((w : K) : V)).2.1
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hmidinj : Function.Injective middle := by
      intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      apply Prod.ext
      · have hx : (((x : K) : V)).1 = 0 := x.property
        have hy : (((y : K) : V)).1 = 0 := y.property
        exact hx.trans hy.symm
      · apply Prod.ext
        · exact hxy
        · exact (hcontain (x : K) (x : K).property).2.trans
            (hcontain (y : K) (y : K).property).2.symm
    have hmid := middle.finrank_le_finrank_of_injective hmidinj
    have hnull := first.finrank_range_add_finrank_ker
    have hdim : Module.finrank (ZMod 2) (Fin a → ZMod 2) = a := by simp
    omega
  let v : V := (![1, 1, 1, 0, 0, 0], 0, 0)
  let w : V := (![1, 1, 0, 1, 0, 0], 0, 0)
  have hv : v ≠ 0 := by intro h; have := congrFun (congrArg Prod.fst h) 0; norm_num [v] at this
  have hw : w ≠ 0 := by intro h; have := congrFun (congrArg Prod.fst h) 0; norm_num [w] at this
  have hvB : Projectivization.mk (ZMod 2) v hv ∈ B := by
    apply (Bmem v hv).2; left; change ![1, 1, 1, 0, 0, 0] ∉ _; decide
  have hwB : Projectivization.mk (ZMod 2) w hw ∈ B := by
    apply (Bmem w hw).2; left; change ![1, 1, 0, 1, 0, 0] ∉ _; decide
  have hne : Projectivization.mk (ZMod 2) v hv ≠ Projectivization.mk (ZMod 2) w hw := by
    intro h
    have hh := congrArg Projectivization.rep h
    rw [rep_mk, rep_mk] at hh
    have hh2 := congrFun (congrArg Prod.fst hh) 2
    change (1 : ZMod 2) = 0 at hh2
    exact one_ne_zero hh2
  have hcard : 1 < B.card := by
    have hs : {Projectivization.mk (ZMod 2) v hv,
        Projectivization.mk (ZMod 2) w hw} ⊆ B := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hvB
      · exact hwB
    have hc := Finset.card_le_card hs
    have hc2 : 2 ≤ B.card := by simpa [hne] using hc
    omega
  let z : V := (Pi.single 0 1, 0, 0)
  have hz : z ≠ 0 := by
    intro h; have := congrFun (congrArg Prod.fst h) 0; norm_num [z] at this
  have hzB : Projectivization.mk (ZMod 2) z hz ∉ B := by
    rw [Bmem]; simp only [not_or]
    constructor
    · change ¬ Pi.single 0 1 ∉ binarySeedDifferences; decide
    · simp [z]
  refine ⟨B, hcard, ?_, block, fun x => (tile x.1, x.2.2), ?_⟩
  · exact ⟨Projectivization.mk (ZMod 2) z hz, hzB⟩
  · intro x y hxy hlabel
    have ht : tile x.1 = tile y.1 := congrArg Prod.fst hlabel
    have hy : x.2.2 = y.2.2 :=
      congrArg (fun p : (Fin 3 → ZMod 2) × (Fin b → ZMod 2) => p.2) hlabel
    rw [Bmem]; simp only [not_or, not_not]
    refine ⟨?_, by simp [hy]⟩
    apply Finset.mem_image.mpr
    refine ⟨(x.1 - binarySeedShift (tile x.1), y.1 - binarySeedShift (tile y.1)),
      Finset.mem_product.mpr ⟨htile x.1, htile y.1⟩, ?_⟩
    dsimp; rw [ht]; abel

end D5.S3.Combinatorics.AdditiveCodes
