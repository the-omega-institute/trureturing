/- GID: D5/S1/Dynamics/Symbolic/LatticeGardenOfEden
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/LatticeGardenOfEden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-neighborhood cellular automata on integer lattices. -/

import D5.S1.Dynamics.Symbolic.GardenOfEden

/-! Local replacements for finite-neighborhood lattice maps. -/

set_option autoImplicit false

noncomputable section

/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license; complete license in
Library/Entropy/diem2026folner.md. Authors: Tom Ole Diem.

Faithful leaf slice from PhyslibAlpha/CondensedMatter/Crystal/Folner.lean
at physlib revision 80ca0ab9dccc5ad8a0f904a6572a728e3abfa125.
Source SHA256: 452431162cd7e05be0b6a17119c21526b7827f705852623a7ab93999f6ed93d9.
Modified packaging: ordinary imports and an isolated namespace retain the
original box-through-tendsto_box_sdiff statements and proof bodies;
the unrelated invariant-state dependency and later declarations are omitted.
Retirement: replace this slice with direct imports when the project's pinned
mathlib supplies equivalent statements for these finite lattice boxes.
-/

namespace CondensedMatter.Crystal

open Finset Filter Topology

/-- The cube `{0, …, m-1}^d` of the lattice `ℤ^d`. -/
def box (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) m

lemma card_box (d m : ℕ) : (box d m).card = m ^ d := by
  simp [box, Fintype.card_piFinset]

lemma image_add_box (d m : ℕ) (h : Fin d → ℤ) :
    (box d m).image (· + h) = Fintype.piFinset fun j => Finset.Ico (h j) (m + h j) := by
  ext x
  simp only [box, mem_image, Fintype.mem_piFinset, mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    have := hy j
    simp only [Pi.add_apply]
    omega
  · intro hx
    refine ⟨x - h, fun j => ?_, by simp⟩
    have := hx j
    simp only [Pi.sub_apply]
    omega

lemma card_image_add_box (d m : ℕ) (h : Fin d → ℤ) : ((box d m).image (· + h)).card = m ^ d := by
  rw [card_image_of_injective _ (add_left_injective h), card_box]

/-- The overlap of the cube with its translate. -/
lemma card_inter_box (d m : ℕ) (h : Fin d → ℤ) :
    ((box d m).image (· + h) ∩ box d m).card =
      ∏ j, (Finset.Ico (h j) (m + h j) ∩ Finset.Ico (0 : ℤ) m).card := by
  rw [image_add_box, box, ← Fintype.piFinset_inter, Fintype.card_piFinset]

/-! ## B. The Følner property -/

lemma card_Ico_inter (m : ℕ) (a : ℤ) (ha : |a| ≤ m) :
    (Finset.Ico a (m + a) ∩ Finset.Ico (0 : ℤ) m).card = m - a.natAbs := by
  rw [Finset.Ico_inter_Ico, Int.card_Ico]
  rw [abs_le] at ha
  omega

/-- The number of points of the cube not shared with its translate. -/
lemma card_sdiff_add_card_sdiff (d m : ℕ) (h : Fin d → ℤ) :
    (((box d m).image (· + h) \ box d m).card + (box d m \ (box d m).image (· + h)).card : ℝ) =
      2 * ((m : ℝ) ^ d - ∏ j, ((Finset.Ico (h j) (m + h j) ∩ Finset.Ico (0 : ℤ) m).card : ℝ)) := by
  have h1 := Finset.card_sdiff_add_card_inter ((box d m).image (· + h)) (box d m)
  have h2 := Finset.card_sdiff_add_card_inter (box d m) ((box d m).image (· + h))
  rw [Finset.inter_comm, card_inter_box] at h2
  rw [card_inter_box, card_image_add_box] at h1
  have h1' : (((box d m).image (· + h) \ box d m).card : ℝ) + (∏ j, ((Finset.Ico (h j) (m + h j) ∩
      Finset.Ico (0 : ℤ) m).card : ℝ)) = (m : ℝ) ^ d := by exact_mod_cast h1
  have h2' : ((box d m \ (box d m).image (· + h)).card : ℝ) + (∏ j, ((Finset.Ico (h j) (m + h j) ∩
      Finset.Ico (0 : ℤ) m).card : ℝ)) = (m : ℝ) ^ d := by
    rw [card_box] at h2; exact_mod_cast h2
  linarith

/-- **The cubes are asymptotically invariant under translation**: the fraction of the points of
`{0, …, n}^d` that are not shared with a fixed translate tends to zero. -/
lemma tendsto_box_sdiff (d : ℕ) (h : Fin d → ℤ) :
    Tendsto (fun n : ℕ => (((box d (n + 1)).image (· + h) \ box d (n + 1)).card +
      (box d (n + 1) \ (box d (n + 1)).image (· + h)).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d)
      atTop (𝓝 0) := by
  have hprod : Tendsto (fun n : ℕ => ∏ j, (((Finset.Ico (h j) ((n + 1 : ℕ) + h j) ∩
      Finset.Ico (0 : ℤ) (n + 1 : ℕ)).card : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (∏ _j : Fin d, 1)) := by
    refine tendsto_finsetProd _ fun j _ => ?_
    have h1 : Tendsto (fun n : ℕ => 1 - ((h j).natAbs : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop (by
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (h j).natAbs] with n hn
    have hab : |h j| ≤ ((n + 1 : ℕ) : ℤ) := by
      calc |h j| = ((h j).natAbs : ℤ) := Int.abs_eq_natAbs _
        _ ≤ _ := by exact_mod_cast (by omega : (h j).natAbs ≤ n + 1)
    rw [card_Ico_inter _ _ hab]
    have hle : (h j).natAbs ≤ n + 1 := by omega
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Nat.cast_sub hle, sub_div, div_self hpos.ne']
  simp only [Finset.prod_const_one] at hprod
  have key : Tendsto (fun n : ℕ => 2 * (1 - ∏ j, (((Finset.Ico (h j) ((n + 1 : ℕ) + h j) ∩
      Finset.Ico (0 : ℤ) (n + 1 : ℕ)).card : ℝ) / ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 (2 * (1 - 1))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hprod)
  rw [sub_self, mul_zero] at key
  refine key.congr fun n => ?_
  rw [card_sdiff_add_card_sdiff, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
  field_simp

end CondensedMatter.Crystal

namespace D5.S1.Dynamics.Symbolic.LatticeGardenOfEden

open Set Function

universe u v

variable {G : Type v} [AddCommGroup G] {A : Type u}

attribute [local instance] Classical.propDecidable

/-- The full configuration map of a rule on a finite neighborhood. -/
def localMap (S : Finset G) (φ : (S → A) → A) (x : G → A) : G → A :=
  fun z => φ (fun s => x (z + s))

/-- Injectivity on pairs of configurations with finite disagreement. -/
def Preinjective (S : Finset G) (φ : (S → A) → A) : Prop :=
  ∀ x y : G → A, Set.Finite {z | x z ≠ y z} → localMap S φ x = localMap S φ y → x = y

private def collar (D S : Finset G) : Finset G := by
  classical
  exact D ∪ D.biUnion (fun a => S.biUnion (fun s => S.image (fun t => a - s + t)))

private theorem mem_collar_core (D S : Finset G) {a : G} (ha : a ∈ D) :
    a ∈ collar D S := by
  classical
  exact Finset.mem_union_left _ ha

private theorem mem_collar_window (D S : Finset G) {a s t : G}
    (ha : a ∈ D) (hs : s ∈ S) (ht : t ∈ S) : a - s + t ∈ collar D S := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨a, ha, Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩⟩)

private theorem localMap_piecewise_of_collar (D S : Finset G) (φ : (S → A) → A)
    {x y z : G → A} (hout : ∀ a, a ∉ D → x a = y a)
    (himage : localMap S φ x = localMap S φ y)
    (hz : ∀ a ∈ collar D S, z a = x a) :
    localMap S φ ((↑(collar D S) : Set G).piecewise y z) = localMap S φ z := by
  classical
  funext a
  by_cases htouch : ∃ s : S, a + s ∈ D
  · obtain ⟨s, hs⟩ := htouch
    have hwindow (t : S) : a + t ∈ collar D S := by
      have hc := mem_collar_window D S hs s.property t.property
      simpa only [add_sub_cancel_right] using hc
    have hp : (fun t : S => (↑(collar D S) : Set G).piecewise y z (a + t)) =
        (fun t : S => y (a + t)) := by
      funext t
      exact Set.piecewise_eq_of_mem _ _ _ (hwindow t)
    change φ (fun t : S => (↑(collar D S) : Set G).piecewise y z (a + t)) =
      φ (fun t : S => z (a + t))
    rw [hp]
    have he : (fun t : S => z (a + t)) = (fun t : S => x (a + t)) :=
      funext (fun t => hz _ (hwindow t))
    rw [he]
    exact (congrFun himage a).symm
  · apply congrArg φ
    funext t
    change (↑(collar D S) : Set G).piecewise y z (a + t) = z (a + t)
    by_cases hc : a + t ∈ collar D S
    · rw [Set.piecewise_eq_of_mem _ _ _ hc]
      exact (hout _ (fun hd => htouch ⟨t, hd⟩)).symm.trans (hz _ hc).symm
    · exact Set.piecewise_eq_of_notMem _ _ _ hc

private theorem finite_context_collision (S : Finset G) (φ : (S → A) → A)
    {x y : G → A} (hf : Set.Finite {a | x a ≠ y a})
    (hi : localMap S φ x = localMap S φ y) (hne : x ≠ y) :
    ∃ C : Finset G, (∀ a, a ∉ C → x a = y a) ∧ (∃ a ∈ C, x a ≠ y a) ∧
      ∀ z : G → A, (∀ a ∈ C, z a = x a) →
        Set.Finite {a | (↑C : Set G).piecewise y z a ≠ z a} ∧
        (↑C : Set G).piecewise y z ≠ z ∧
        localMap S φ ((↑C : Set G).piecewise y z) = localMap S φ z := by
  classical
  let D := hf.toFinset
  have hout (a : G) (ha : a ∉ D) : x a = y a := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using ha
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have haD : a ∈ D := by simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
  have haC := mem_collar_core D S haD
  refine ⟨collar D S, (fun b hb => hout b (fun hd => hb (mem_collar_core D S hd))),
    ⟨a, haC, ha⟩, ?_⟩
  intro z hz
  refine ⟨(collar D S).finite_toSet.subset ?_, ?_, localMap_piecewise_of_collar D S φ hout hi hz⟩
  · intro b hb
    by_contra hc
    exact hb (Set.piecewise_eq_of_notMem _ _ _ hc)
  · intro he
    have he' := congrFun he a
    rw [Set.piecewise_eq_of_mem _ _ _ haC, hz _ haC] at he'
    exact ha he'.symm

private def writePattern (C : Finset G) (p : C → A) (t : G) (x : G → A) : G → A :=
  fun a => if h : a - t ∈ C then p ⟨a - t, h⟩ else x a

private theorem writePattern_at (C : Finset G) (p : C → A) (t : G) (x : G → A)
    (c : C) : writePattern C p t x (t + c) = p c := by
  simp only [writePattern, add_sub_cancel_left]
  exact dite_eq_left c.property

private theorem exists_erasable_shape (S : Finset G) (φ : (S → A) → A)
    {x y : G → A} (hf : Set.Finite {a | x a ≠ y a})
    (hi : localMap S φ x = localMap S φ y) (hne : x ≠ y) :
    ∃ C : Finset G, ∃ p q : C → A, p ≠ q ∧
      ∀ (t : G) (z : G → A), (∀ c : C, z (t + c) = p c) →
        localMap S φ (writePattern C q t z) = localMap S φ z := by
  classical
  obtain ⟨C, _, ⟨a, haC, ha⟩, hreplace⟩ := finite_context_collision S φ hf hi hne
  let p : C → A := fun c => x c
  let q : C → A := fun c => y c
  refine ⟨C, p, q, (fun he => ha (congrFun he ⟨a, haC⟩)), ?_⟩
  intro t z hz
  let z' : G → A := fun b => z (t + b)
  have hz' : ∀ b ∈ C, z' b = x b := fun b hb => hz ⟨b, hb⟩
  have he := (hreplace z' hz').2.2
  funext b
  have he' := congrFun he (b - t)
  change φ (fun s : S => (↑C : Set G).piecewise y z' (b - t + s)) =
    φ (fun s : S => z' (b - t + s)) at he'
  have hw : (fun s : S => writePattern C q t z (b + s)) =
      (fun s : S => (↑C : Set G).piecewise y z' (b - t + s)) := by
    funext s
    have ht : b + (s : G) - t = b - t + s := by abel
    dsimp only [writePattern]
    rw [ht]
    split_ifs with hc
    · exact (Set.piecewise_eq_of_mem _ _ _ hc).symm
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc]
      dsimp [z']
      congr 1
      abel
  change φ (fun s : S => writePattern C q t z (b + s)) = φ (fun s : S => z (b + s))
  rw [hw, he']
  congr 1
  funext s
  dsimp [z']
  congr 1
  abel

private theorem erase_disjoint_patterns (S : Finset G) (φ : (S → A) → A)
    (C : Finset G) (p q : C → A) (hpq : p ≠ q)
    (herase : ∀ (t : G) (z : G → A), (∀ c : C, z (t + c) = p c) →
      localMap S φ (writePattern C q t z) = localMap S φ z)
    (T : Finset G)
    (hdis : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t + c ≠ u + e)
    (x : G → A) :
    ∃ y : G → A, localMap S φ y = localMap S φ x ∧
      ∀ t ∈ T, (fun c : C => y (t + c)) ≠ p := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨x, rfl, by simp⟩
  | @insert t T ht ih =>
    obtain ⟨y, hy, hay⟩ := ih (fun u hu v hv huv =>
      hdis u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv)
    by_cases hc : (fun c : C => y (t + c)) = p
    · refine ⟨writePattern C q t y, (herase t y (fun c => congrFun hc c)).trans hy, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simpa only [writePattern_at] using hpq.symm
      · have heq : (fun c : C => writePattern C q t y (u + c)) =
            (fun c : C => y (u + c)) := by
          funext c
          apply dite_eq_right
          intro hh
          have hn := hdis t (Finset.mem_insert_self _ _) u (Finset.mem_insert_of_mem hu)
            (fun he => ht (he ▸ hu)) ⟨u + c - t, hh⟩ c
          apply hn
          change t + (u + (c : G) - t) = u + c
          abel
        rw [heq]
        exact hay u hu
    · exact ⟨y, hy, fun u hu => by
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hc
        · exact hay u hu⟩

private theorem exists_dense_packing (C F : Finset G) (hC : C.Nonempty) :
    ∃ T : Finset G, T ⊆ F ∧
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t + c ≠ u + e) ∧
      F.card ≤ T.card * C.card ^ 2 := by
  classical
  let good (T : Finset G) :=
    ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t + c ≠ u + e
  let candidates := F.powerset.filter good
  have he : (∅ : Finset G) ∈ candidates := by simp [candidates, good]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, he⟩
  have hsub : T ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hgood : good T := (Finset.mem_filter.mp hT).2
  have hcover (f : F) : ∃ t : T, ∃ c e : C, (f : G) + c = (t : G) + e := by
    by_contra hn
    have hn' : ∀ t : T, ∀ c e : C, (f : G) + c ≠ (t : G) + e := by
      simpa only [not_exists] using hn
    have hfT : (f : G) ∉ T := by
      intro hfT
      obtain ⟨c, hc⟩ := hC
      exact hn' ⟨f, hfT⟩ ⟨c, hc⟩ ⟨c, hc⟩ rfl
    have hg : good (insert (f : G) T) := by
      intro t ht u hu htu c e
      rcases Finset.mem_insert.mp ht with rfl | ht
      · rcases Finset.mem_insert.mp hu with rfl | hu
        · exact (htu rfl).elim
        · exact hn' ⟨u, hu⟩ c e
      · rcases Finset.mem_insert.mp hu with rfl | hu
        · exact (hn' ⟨t, ht⟩ e c).symm
        · exact hgood t ht u hu htu c e
    have hi : insert (f : G) T ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.insert_subset f.property hsub), hg⟩
    have hm := hmax _ hi
    rw [Finset.card_insert_of_notMem hfT] at hm
    omega
  choose t c e hkey using hcover
  let key : F → T × C × C := fun f => (t f, c f, e f)
  have hk : Injective key := by
    intro f g heq
    have ht := congrArg (fun a : T × C × C => (a.1 : G)) heq
    have hc := congrArg (fun a : T × C × C => (a.2.1 : G)) heq
    have he := congrArg (fun a : T × C × C => (a.2.2 : G)) heq
    dsimp only [key] at ht hc he
    apply Subtype.ext
    have hfg : (f : G) + c f = (g : G) + c f := by
      calc
        _ = (t f : G) + e f := hkey f
        _ = (t g : G) + e g := by rw [ht, he]
        _ = (g : G) + c g := (hkey g).symm
        _ = _ := by rw [hc]
    exact add_right_cancel hfg
  refine ⟨T, hsub, hgood, ?_⟩
  have hcard := Nat.card_le_card_of_injective key hk
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod, pow_two,
    Nat.mul_assoc] using hcard

private theorem cardinal_bound_of_disjoint_avoidance [Finite A]
    {O : Type*} (U C T : Finset G) (p : C → A) (norm : O → G → A)
    (hdis : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t + c ≠ u + e)
    (hinside : ∀ t ∈ T, ∀ c ∈ C, t + c ∈ U)
    (havoid : ∀ o t, t ∈ T → (fun c : C => norm o (t + c)) ≠ p)
    (hdet : ∀ o o', (∀ a ∈ U, norm o a = norm o' a) → o = o') :
    Nat.card O ≤ (Nat.card A ^ C.card - 1) ^ T.card *
      Nat.card A ^ (U.card - T.card * C.card) ∧ T.card * C.card ≤ U.card := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let B := {w : C → A // w ≠ p}
  let K := T.biUnion (fun t => C.image (fun c => t + c))
  let R := U \ K
  have hKU : K ⊆ U := by
    intro a ha
    obtain ⟨t, ht, hm⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    exact hinside t ht b hb
  have hK : K.card = T.card * C.card := by
    have hd : (↑T : Set G).PairwiseDisjoint (fun t => C.image (fun c => t + c)) := by
      intro t ht u hu htu
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      obtain ⟨e, he, hea⟩ := Finset.mem_image.mp hb
      exact hdis t ht u hu htu ⟨c, hc⟩ ⟨e, he⟩ (hca.trans hea.symm)
    dsimp only [K]
    rw [Finset.card_biUnion hd]
    simp only [Finset.card_image_of_injective _ (add_right_injective _),
      Finset.sum_const, smul_eq_mul]
  let key : O → (T → B) × (R → A) := fun o =>
    (fun t => ⟨fun c => norm o (t + c), havoid o t t.property⟩,
      fun r => norm o r)
  have hkey : Injective key := by
    intro o o' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    apply hdet
    intro a ha
    by_cases hk : a ∈ K
    · obtain ⟨t, ht, hm⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hm
      exact congrFun (congrArg Subtype.val (congrFun he1 ⟨t, ht⟩)) ⟨c, hc⟩
    · exact congrFun he2 ⟨a, Finset.mem_sdiff.mpr ⟨ha, hk⟩⟩
  have hB : Fintype.card B = Fintype.card A ^ C.card - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun w : C → A => w = p)]
    simp
  have hR : Fintype.card R = U.card - T.card * C.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset hKU, hK]
  have hc := Nat.card_le_card_of_injective key hkey
  refine ⟨?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_coe, hB, hR] using hc
  · rw [← hK]
    exact Finset.card_le_card hKU

private def pad (F E : Finset G) : Finset G := by
  classical
  exact E.biUnion (fun e => F.image (fun f => f + e))

private theorem mem_pad {F E : Finset G} {f e : G} (hf : f ∈ F) (he : e ∈ E) :
    f + e ∈ pad F E := by
  classical
  exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

/-- Patterns obtained by restricting one complete image configuration. -/
def ImagePatterns (S : Finset G) (φ : (S → A) → A) (F : Finset G) :=
  Set.range (fun x : G → A => fun f : F => localMap S φ x f)

private theorem collision_image_bound [Finite A]
    (S : Finset G) (φ : (S → A) → A) (C : Finset G) (p q : C → A) (hpq : p ≠ q)
    (herase : ∀ (t : G) (z : G → A), (∀ c : C, z (t + c) = p c) →
      localMap S φ (writePattern C q t z) = localMap S φ z) (F : Finset G) :
    ∃ T : Finset G, F.card ≤ T.card * C.card ^ 2 ∧
      Nat.card (ImagePatterns S φ F) ≤ (Nat.card A ^ C.card - 1) ^ T.card *
        Nat.card A ^ ((pad F (insert 0 (S ∪ C))).card - T.card * C.card) ∧
      T.card * C.card ≤ (pad F (insert 0 (S ∪ C))).card := by
  classical
  obtain ⟨c, _⟩ := Function.ne_iff.mp hpq
  obtain ⟨T, hTF, hdis, hdense⟩ := exists_dense_packing C F ⟨c, c.property⟩
  let source (o : ImagePatterns S φ F) : G → A := Classical.choose o.property
  have hs (o : ImagePatterns S φ F) (f : F) : localMap S φ (source o) f = o.val f :=
    congrFun (Classical.choose_spec o.property) f
  have hn (o : ImagePatterns S φ F) := erase_disjoint_patterns S φ C p q hpq herase T hdis (source o)
  choose norm hnorm havoid using hn
  have hinside : ∀ t ∈ T, ∀ c ∈ C, t + c ∈ pad F (insert 0 (S ∪ C)) := by
    intro t ht c hc
    exact mem_pad (hTF ht) (Finset.mem_insert_of_mem (Finset.mem_union_right _ hc))
  have hdet (o o' : ImagePatterns S φ F)
      (he : ∀ a ∈ pad F (insert 0 (S ∪ C)), norm o a = norm o' a) : o = o' := by
    apply Subtype.ext
    funext f
    calc
      o.val f = localMap S φ (norm o) f := ((congrFun (hnorm o) f).trans (hs o f)).symm
      _ = localMap S φ (norm o') f := by
        apply congrArg φ
        funext s
        exact he _ (mem_pad f.property
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ s.property)))
      _ = o'.val f := (congrFun (hnorm o') f).trans (hs o' f)
  exact ⟨T, hdense, cardinal_bound_of_disjoint_avoidance
    (pad F (insert 0 (S ∪ C))) C T p norm hdis hinside havoid hdet⟩

end D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
