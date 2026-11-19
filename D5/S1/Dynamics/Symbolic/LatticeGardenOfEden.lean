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
support lemmas are private, and the unrelated invariant-state dependency
and later declarations are omitted.
Retirement: replace this slice with direct imports when the project's pinned
mathlib supplies equivalent statements for these finite lattice boxes.
-/

namespace CondensedMatter.Crystal

open Finset Filter Topology

/-- The cube `{0, …, m-1}^d` of the lattice `ℤ^d`. -/
def box (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) m

private lemma card_box (d m : ℕ) : (box d m).card = m ^ d := by
  simp [box, Fintype.card_piFinset]

private lemma image_add_box (d m : ℕ) (h : Fin d → ℤ) :
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

private lemma card_image_add_box (d m : ℕ) (h : Fin d → ℤ) :
    ((box d m).image (· + h)).card = m ^ d := by
  rw [card_image_of_injective _ (add_left_injective h), card_box]

/-- The overlap of the cube with its translate. -/
private lemma card_inter_box (d m : ℕ) (h : Fin d → ℤ) :
    ((box d m).image (· + h) ∩ box d m).card =
      ∏ j, (Finset.Ico (h j) (m + h j) ∩ Finset.Ico (0 : ℤ) m).card := by
  rw [image_add_box, box, ← Fintype.piFinset_inter, Fintype.card_piFinset]

/-! ## B. The Følner property -/

private lemma card_Ico_inter (m : ℕ) (a : ℤ) (ha : |a| ≤ m) :
    (Finset.Ico a (m + a) ∩ Finset.Ico (0 : ℤ) m).card = m - a.natAbs := by
  rw [Finset.Ico_inter_Ico, Int.card_Ico]
  rw [abs_le] at ha
  omega

/-- The number of points of the cube not shared with its translate. -/
private lemma card_sdiff_add_card_sdiff (d m : ℕ) (h : Fin d → ℤ) :
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
private lemma tendsto_box_sdiff (d : ℕ) (h : Fin d → ℤ) :
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

variable {G : Type v} [AddCommGroup G] [DecidableEq G] {A : Type u}

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

omit [DecidableEq G] in
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

omit [DecidableEq G] in
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

/-- Cardinality of the jointly realized full-image patterns on a finite shape. -/
def imagePatternCount (F : Finset G) (S : Finset G) (φ : (S → A) → A) : ℕ :=
  Nat.card (ImagePatterns S φ F)

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
  have hn (o : ImagePatterns S φ F) :=
    erase_disjoint_patterns S φ C p q hpq herase T hdis (source o)
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

private theorem pad_card_le_boundary (F E : Finset G) :
    (pad F E).card ≤ F.card + ∑ e ∈ E,
      (((F.image (fun f => f + e)) \ F).card + (F \ (F.image (fun f => f + e))).card) := by
  classical
  have hd : pad F E \ F = E.biUnion (fun e => (F.image (fun f => f + e)) \ F) := by
    ext a
    simp only [pad, Finset.mem_sdiff, Finset.mem_biUnion]
    aesop
  calc
    (pad F E).card ≤ (pad F E \ F).card + F.card := Finset.card_le_card_sdiff_add_card
    _ = (E.biUnion (fun e => (F.image (fun f => f + e)) \ F)).card + F.card := by rw [hd]
    _ ≤ (∑ e ∈ E, ((F.image (fun f => f + e)) \ F).card) + F.card :=
      Nat.add_le_add_right Finset.card_biUnion_le _
    _ ≤ F.card + ∑ e ∈ E,
        (((F.image (fun f => f + e)) \ F).card + (F \ (F.image (fun f => f + e))).card) := by
      rw [Nat.add_comm]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun e _ => Nat.le_add_right _ _)) _

open CondensedMatter.Crystal Filter Topology

private theorem pad_box_ratio (d : ℕ) (E : Finset (Fin d → ℤ)) (hE : 0 ∈ E) :
    Tendsto (fun n : ℕ => ((pad (box d (n + 1)) E).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d)
      atTop (𝓝 1) := by
  classical
  let boundary (n : ℕ) := ∑ e ∈ E,
    ((((box d (n + 1)).image (fun f => f + e) \ box d (n + 1)).card +
      (box d (n + 1) \ (box d (n + 1)).image (fun f => f + e)).card : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ d)
  have hb : Tendsto boundary atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, boundary] using
      (tendsto_finsetSum E (fun e _ => tendsto_box_sdiff d e))
  have hl (n : ℕ) : 0 ≤ ((pad (box d (n + 1)) E).card : ℝ) /
      ((n + 1 : ℕ) : ℝ) ^ d - 1 := by
    have hsub : box d (n + 1) ⊆ pad (box d (n + 1)) E := by
      intro a ha
      simpa only [add_zero] using mem_pad ha hE
    have hc : (((n + 1) ^ d : ℕ) : ℝ) ≤ ((pad (box d (n + 1)) E).card : ℝ) := by
      exact_mod_cast (show (n + 1) ^ d ≤ (pad (box d (n + 1)) E).card by
        rw [← card_box]; exact Finset.card_le_card hsub)
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
    rw [sub_nonneg, le_div_iff₀ hp, one_mul]
    simpa only [Nat.cast_pow] using hc
  have hu (n : ℕ) : ((pad (box d (n + 1)) E).card : ℝ) /
      ((n + 1 : ℕ) : ℝ) ^ d - 1 ≤ boundary n := by
    have hc := pad_card_le_boundary (box d (n + 1)) E
    rw [card_box] at hc
    have hc' := (Nat.cast_le (α := ℝ)).mpr hc
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_sum] at hc'
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
    have hh := div_le_div_of_nonneg_right hc' hp.le
    simp only [Nat.cast_add] at hp hh
    rw [add_div, div_self hp.ne'] at hh
    dsimp only [boundary]
    rw [← Finset.sum_div]
    simp only [Nat.cast_add] at hh ⊢
    linarith
  have hzero := squeeze_zero hl hu hb
  convert hzero.add_const 1 using 1 <;> simp

theorem logarithmic_packing_bound {a b k u v f : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hv : 0 < v) (hf : 0 < f)
    (hdense : v ≤ k * b ^ 2) (hinside : k * b ≤ u)
    (hcount : f ≤ (a ^ b - 1) ^ k * a ^ (u - k * b)) :
    0 < ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2 ∧
    Real.log (f : ℝ) / v ≤ (u : ℝ) / v * Real.log (a : ℝ) -
      ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : 1 < a ^ b := one_lt_pow' (by omega) hb.ne'
  have hB : (0 : ℝ) < (a ^ b - 1 : ℕ) := by exact_mod_cast (show 0 < a ^ b - 1 by omega)
  have hlt : ((a ^ b - 1 : ℕ) : ℝ) < (a : ℝ) ^ b := by
    exact_mod_cast (show a ^ b - 1 < a ^ b by omega)
  have hL : 0 < (b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ) := by
    have hh := Real.log_lt_log hB hlt
    rw [Real.log_pow] at hh
    linarith
  have hlog : Real.log (f : ℝ) ≤ (k : ℝ) * Real.log (a ^ b - 1 : ℕ) +
      ((u : ℝ) - (k : ℝ) * b) * Real.log (a : ℝ) := by
    calc
      _ ≤ Real.log (((a ^ b - 1 : ℕ) : ℝ) ^ k * (a : ℝ) ^ (u - k * b)) :=
        Real.log_le_log (by exact_mod_cast hf) (by exact_mod_cast hcount)
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
          Nat.cast_sub hinside, Nat.cast_mul]
  have hd : (v : ℝ) / (b : ℝ) ^ 2 ≤ k := by
    apply (div_le_iff₀ (sq_pos_of_pos hb0)).mpr
    exact_mod_cast hdense
  have hcharge := mul_le_mul_of_nonneg_right hd hL.le
  have hcharge' : (v : ℝ) *
      (((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2) ≤
        (k : ℝ) * ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) := by
    convert hcharge using 1
    ring
  have hresult : Real.log (f : ℝ) ≤ (u : ℝ) * Real.log (a : ℝ) -
      (v : ℝ) * (((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) /
        (b : ℝ) ^ 2) := by
    nlinarith only [hlog, hcharge']
  refine ⟨div_pos hL (sq_pos_of_pos hb0), ?_⟩
  apply (div_le_iff₀ hv0).mpr
  calc
    _ ≤ _ := hresult
    _ = _ := by field_simp

omit [DecidableEq G] in
private theorem imagePatterns_card_pos [Finite A] (S : Finset G) (φ : (S → A) → A)
    (x : G → A) (F : Finset G) : 0 < Nat.card (ImagePatterns S φ F) := by
  have : Nonempty (ImagePatterns S φ F) := ⟨⟨fun f => localMap S φ x f, x, rfl⟩⟩
  exact Nat.card_pos

/-- A finite collision forces a strict eventual logarithmic deficit in the
patterns jointly realized by complete image configurations on lattice boxes. -/
theorem strict_image_box_loss [Finite A] (d : ℕ) (_hd : 1 ≤ d)
    (S : Finset (Fin d → ℤ)) (φ : (S → A) → A) (ha : 2 ≤ Nat.card A)
    (x y : (Fin d → ℤ) → A) (hf : Set.Finite {z | x z ≠ y z})
    (hi : localMap S φ x = localMap S φ y) (hne : x ≠ y) :
    ∃ c : ℝ, c < Real.log (Nat.card A : ℝ) ∧ ∃ N : ℕ, ∀ n ≥ N,
      Real.log (imagePatternCount (box d (n + 1)) S φ : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ d ≤ c := by
  classical
  obtain ⟨C, p, q, hpq, herase⟩ := exists_erasable_shape S φ hf hi hne
  obtain ⟨e, _⟩ := Function.ne_iff.mp hpq
  have hb : 0 < C.card := Finset.card_pos.mpr ⟨e, e.property⟩
  let δ := ((C.card : ℝ) * Real.log (Nat.card A : ℝ) -
    Real.log (Nat.card A ^ C.card - 1 : ℕ)) / (C.card : ℝ) ^ 2
  let E := insert 0 (S ∪ C)
  have hbound (n : ℕ) : 0 < δ ∧
      Real.log (Nat.card (ImagePatterns S φ (box d (n + 1))) : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ d ≤
      ((pad (box d (n + 1)) E).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d *
        Real.log (Nat.card A : ℝ) - δ := by
    obtain ⟨T, hdense, hcount, hinside⟩ := collision_image_bound S φ C p q hpq herase
      (box d (n + 1))
    have hh := logarithmic_packing_bound ha hb
      (show 0 < (box d (n + 1)).card by rw [card_box]; positivity)
      (imagePatterns_card_pos S φ x _) hdense hinside hcount
    simpa only [card_box, Nat.cast_pow] using hh
  have hδ : 0 < δ := (hbound 0).1
  let c := Real.log (Nat.card A : ℝ) - δ / 2
  have hc : Real.log (Nat.card A : ℝ) - δ < c := by dsimp [c]; linarith
  have hlim : Tendsto
      (fun n : ℕ => ((pad (box d (n + 1)) E).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d *
        Real.log (Nat.card A : ℝ) - δ) atTop (𝓝 (Real.log (Nat.card A : ℝ) - δ)) := by
    simpa only [one_mul] using ((pad_box_ratio d E (Finset.mem_insert_self _ _)).mul_const
      (Real.log (Nat.card A : ℝ))).sub_const δ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hc))
  refine ⟨c, by dsimp [c]; linarith, N, ?_⟩
  intro n hn
  exact (hbound n).2.trans (hN n hn).le

omit [DecidableEq G] in
private theorem missing_pattern_of_not_surjective [Finite A]
    (S : Finset G) (φ : (S → A) → A) (hns : ¬ Surjective (localMap S φ)) :
    ∃ C : Finset G, C.Nonempty ∧ ∃ p : C → A,
      ∀ (x : G → A) (t : G), (fun c : C => localMap S φ x (t + c)) ≠ p := by
  classical
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hcont : Continuous (localMap S φ) := by
    apply continuous_pi
    intro z
    exact continuous_of_discreteTopology.comp (continuous_pi (fun s : S =>
      continuous_apply (z + s)))
  have hclosed : IsClosed (range (localMap S φ)) := (isCompact_range hcont).isClosed
  obtain ⟨y, hy⟩ : ∃ y : G → A, y ∉ range (localMap S φ) := by
    simpa only [Surjective, mem_range, not_forall] using hns
  obtain ⟨C, U, hU, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl y hy
  have hC : C.Nonempty := by
    by_contra hn
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : localMap S φ y ∈ (↑C : Set G).pi U := by simp [he]
    exact hsub hm ⟨y, rfl⟩
  refine ⟨C, hC, (fun c => y c), ?_⟩
  intro x t he
  let x' : G → A := fun a => x (t + a)
  have hm : localMap S φ x' ∈ (↑C : Set G).pi U := by
    intro c hc
    have he' := congrFun he ⟨c, hc⟩
    have hshift : localMap S φ x' c = localMap S φ x (t + c) := by
      apply congrArg φ
      funext s
      dsimp [x']
      congr 1
      abel
    rw [hshift, he']
    exact (hU c hc).2
  exact hsub hm ⟨x', rfl⟩

omit [DecidableEq G] in
private theorem missing_image_bound [Finite A]
    (S : Finset G) (φ : (S → A) → A) (C : Finset G) (hC : C.Nonempty) (p : C → A)
    (hmissing : ∀ (x : G → A) (t : G), (fun c : C => localMap S φ x (t + c)) ≠ p)
    (F B U : Finset G) (hFU : F ⊆ U) (hin : ∀ t ∈ B, ∀ c ∈ C, t + c ∈ U) :
    ∃ T : Finset G, B.card ≤ T.card * C.card ^ 2 ∧
      Nat.card (ImagePatterns S φ F) ≤ (Nat.card A ^ C.card - 1) ^ T.card *
        Nat.card A ^ (U.card - T.card * C.card) ∧ T.card * C.card ≤ U.card := by
  classical
  obtain ⟨T, hTB, hdis, hdense⟩ := exists_dense_packing C B hC
  let source (o : ImagePatterns S φ F) : G → A := Classical.choose o.property
  let norm (o : ImagePatterns S φ F) : G → A := localMap S φ (source o)
  have hs (o : ImagePatterns S φ F) (f : F) : norm o f = o.val f :=
    congrFun (Classical.choose_spec o.property) f
  have hdet (o o' : ImagePatterns S φ F)
      (he : ∀ a ∈ U, norm o a = norm o' a) : o = o' := by
    apply Subtype.ext
    funext f
    exact (hs o f).symm.trans ((he f (hFU f.property)).trans (hs o' f))
  exact ⟨T, hdense, cardinal_bound_of_disjoint_avoidance U C T p norm hdis
    (fun t ht => hin t (hTB ht)) (fun o t _ => hmissing (source o) t) hdet⟩

private theorem preinjective_pattern_lower [Finite A] [Nonempty A]
    (S : Finset G) (φ : (S → A) → A) (hp : Preinjective S φ) (F : Finset G) :
    Nat.card A ^ F.card ≤
      Nat.card (ImagePatterns S φ (pad F (insert 0 (S.image (fun s => -s))))) := by
  classical
  let a : A := Classical.choice ‹Nonempty A›
  let lift (w : F → A) : G → A := fun z => if hz : z ∈ F then w ⟨z, hz⟩ else a
  let E := insert 0 (S.image (fun s => -s))
  let key : (F → A) → ImagePatterns S φ (pad F E) := fun w =>
    ⟨fun z => localMap S φ (lift w) z, lift w, rfl⟩
  have hk : Injective key := by
    intro w v he
    have hf : Set.Finite {z | lift w z ≠ lift v z} := by
      apply F.finite_toSet.subset
      intro z hz
      by_contra hn
      exact hz (by
        dsimp only [lift]
        split_ifs with h
        · exact (hn h).elim
        · rfl)
    have hi : localMap S φ (lift w) = localMap S φ (lift v) := by
      funext z
      by_cases hz : z ∈ pad F E
      · exact congrFun (congrArg Subtype.val he) ⟨z, hz⟩
      · apply congrArg φ
        funext s
        have hout : z + (s : G) ∉ F := by
          intro hin
          have hneg : -(s : G) ∈ E := Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨(s : G), s.property, rfl⟩)
          have hm := mem_pad hin hneg
          exact hz (by simpa only [add_neg_cancel_right] using hm)
        simp only [lift, dite_eq_right hout]
    have hinput := hp (lift w) (lift v) hf hi
    funext z
    have hh := congrFun hinput z
    simpa only [lift, dite_eq_left z.property] using hh
  have hc := Nat.card_le_card_of_injective key hk
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

omit [DecidableEq G] in
private theorem surjective_patterns_full [Finite A] [Nonempty A]
    (S : Finset G) (φ : (S → A) → A) (hs : Surjective (localMap S φ)) (F : Finset G) :
    Nat.card (ImagePatterns S φ F) = Nat.card A ^ F.card := by
  classical
  have hfull : ImagePatterns S φ F = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    let z : G → A := fun a => if ha : a ∈ F then w ⟨a, ha⟩ else Classical.choice ‹Nonempty A›
    obtain ⟨x, hx⟩ := hs z
    refine ⟨x, ?_⟩
    funext f
    exact (congrFun hx f).trans (by simp only [z, dite_eq_left f.property])
  rw [hfull, Nat.card_univ, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ↥F), Fintype.card_coe]

private theorem surjective_of_preinjective [Finite A] [Nonempty A]
    (d : ℕ) (S : Finset (Fin d → ℤ)) (φ : (S → A) → A)
    (ha : 2 ≤ Nat.card A) (hp : Preinjective S φ) : Surjective (localMap S φ) := by
  classical
  by_contra hns
  obtain ⟨C, hC, p, hmissing⟩ := missing_pattern_of_not_surjective S φ hns
  let negS := S.image (fun s => -s)
  let E0 := insert 0 negS
  let E := insert 0 (negS ∪ C)
  let δ := ((C.card : ℝ) * Real.log (Nat.card A : ℝ) -
    Real.log (Nat.card A ^ C.card - 1 : ℕ)) / (C.card : ℝ) ^ 2
  have ha0 : (0 : ℝ) < Nat.card A := by exact_mod_cast (show 0 < Nat.card A by omega)
  let x : (Fin d → ℤ) → A := fun _ => Classical.choice ‹Nonempty A›
  have hbound (n : ℕ) : 0 < δ ∧ Real.log (Nat.card A : ℝ) ≤
      ((pad (box d (n + 1)) E).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d *
        Real.log (Nat.card A : ℝ) - δ := by
    let B := box d (n + 1)
    let F := pad B E0
    let U := pad B E
    have hFU : F ⊆ U := by
      intro a ha
      obtain ⟨e, he, hm⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_biUnion.mpr ⟨e, (by
        rcases Finset.mem_insert.mp he with rfl | he
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)), hm⟩
    have hin : ∀ t ∈ B, ∀ c ∈ C, t + c ∈ U := by
      intro t ht c hc
      exact mem_pad ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ hc))
    obtain ⟨T, hdense, hcount, hinside⟩ := missing_image_bound S φ C hC p hmissing F B U hFU hin
    have hv : 0 < B.card := by dsimp [B]; rw [card_box]; positivity
    have hlog := logarithmic_packing_bound ha (Finset.card_pos.mpr hC) hv
      (imagePatterns_card_pos S φ x F) hdense hinside hcount
    have hlower := preinjective_pattern_lower S φ hp B
    change Nat.card A ^ B.card ≤ Nat.card (ImagePatterns S φ F) at hlower
    have hloglower : Real.log (Nat.card A : ℝ) ≤
        Real.log (Nat.card (ImagePatterns S φ F) : ℝ) / B.card := by
      have hc : (Nat.card A : ℝ) ^ B.card ≤ (Nat.card (ImagePatterns S φ F) : ℝ) := by
        exact_mod_cast hlower
      have hh := Real.log_le_log (pow_pos ha0 B.card) hc
      rw [Real.log_pow] at hh
      apply (le_div_iff₀ (by exact_mod_cast hv : (0 : ℝ) < B.card)).mpr
      simpa only [mul_comm] using hh
    refine ⟨hlog.1, ?_⟩
    have hh := hloglower.trans hlog.2
    simpa only [B, U, card_box, Nat.cast_pow] using hh
  have hδ := (hbound 0).1
  have hlim : Tendsto
      (fun n : ℕ => ((pad (box d (n + 1)) E).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d *
        Real.log (Nat.card A : ℝ) - δ) atTop (𝓝 (Real.log (Nat.card A : ℝ) - δ)) := by
    simpa only [one_mul] using ((pad_box_ratio d E (Finset.mem_insert_self _ _)).mul_const
      (Real.log (Nat.card A : ℝ))).sub_const δ
  have hh : Real.log (Nat.card A : ℝ) ≤ Real.log (Nat.card A : ℝ) - δ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall (fun n => (hbound n).2))
  linarith

private theorem rank_one_from_native [Finite A]
    (S : Finset (Fin 1 → ℤ)) (φ : (S → A) → A) :
    Surjective (localMap S φ) ↔ Preinjective S φ := by
  classical
  let site : ℤ ≃ (Fin 1 → ℤ) := {
    toFun := fun i _ => i
    invFun := fun z => z 0
    left_inv := fun _ => rfl
    right_inv := by intro z; funext j; rw [Subsingleton.elim j 0] }
  let e : (ℤ → A) ≃ ((Fin 1 → ℤ) → A) := Equiv.arrowCongr site (Equiv.refl A)
  let R := S.sup (fun s => (s 0).natAbs)
  have hR (s : S) : -(R : ℤ) ≤ (s : Fin 1 → ℤ) 0 ∧ (s : Fin 1 → ℤ) 0 ≤ R := by
    apply abs_le.mp
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (Finset.le_sup (f := fun z : Fin 1 → ℤ => (z 0).natAbs)
      s.property : ((s : Fin 1 → ℤ) 0).natAbs ≤ R)
  let idx (s : S) : Fin (2 * R + 2) := ⟨((s : Fin 1 → ℤ) 0 + R).toNat, by
    have hh := hR s
    omega⟩
  let H : (Fin (2 * R + 2) → A) → A := fun w => φ (fun s => w (idx s))
  let shift : (ℤ → A) ≃ (ℤ → A) := {
    toFun := fun y i => y (i + R)
    invFun := fun y i => y (i - R)
    left_inv := by intro y; funext i; simp
    right_inv := by intro y; funext i; simp }
  let o := e.symm.trans shift
  let N := PermutativeLifts.BipermutativeLift.code H
  have hcomm (x : ℤ → A) : N x = o (localMap S φ (e x)) := by
    funext i
    apply congrArg φ
    funext s
    change x (i + (idx s : ℕ)) = x (i + (R : ℤ) + (s : Fin 1 → ℤ) 0)
    apply congrArg x
    have hh := hR s
    dsimp only [idx]
    omega
  have hsurj : Surjective N ↔ Surjective (localMap S φ) := by
    constructor
    · intro hn y
      obtain ⟨x, hx⟩ := hn (o y)
      exact ⟨e x, o.injective ((hcomm x).symm.trans hx)⟩
    · intro hp y
      obtain ⟨z, hz⟩ := hp (o.symm y)
      refine ⟨e.symm z, ?_⟩
      rw [hcomm, e.apply_symm_apply, hz, o.apply_symm_apply]
  have hfinite (x y : ℤ → A) : Set.Finite {z | e x z ≠ e y z} ↔
      Set.Finite {i | x i ≠ y i} := by
    constructor
    · intro hf
      exact Set.Finite.preimage site.injective.injOn hf
    · intro hf
      exact Set.Finite.preimage site.symm.injective.injOn hf
  have hpre : PermutativeLifts.BipermutativePreinjectivity.Preinjective H ↔ Preinjective S φ := by
    constructor
    · intro hp x y hf hi
      have hfi := (hfinite (e.symm x) (e.symm y)).mp (by simpa only [e.apply_symm_apply] using hf)
      have hNi : N (e.symm x) = N (e.symm y) := by
        rw [hcomm, hcomm, e.apply_symm_apply, e.apply_symm_apply, hi]
      exact e.symm.injective (hp hfi hNi)
    · intro hp x y hf hi
      apply e.injective
      apply hp (e x) (e y) ((hfinite x y).mpr hf)
      exact o.injective ((hcomm x).symm.trans (hi.trans (hcomm y)))
  exact hsurj.symm.trans ((GardenOfEden.garden_of_eden (2 * R) H).trans hpre)

/-- The Moore–Myhill theorem on every finite-dimensional integer lattice,
with arbitrary finite neighborhood and arbitrary finite alphabet. -/
theorem garden_of_eden [Finite A] (d : ℕ) (S : Finset (Fin d → ℤ)) (φ : (S → A) → A) :
    Surjective (localMap S φ) ↔ Preinjective S φ := by
  classical
  by_cases hA : Subsingleton A
  · let : Subsingleton A := hA
    exact ⟨fun _ _ _ _ _ => Subsingleton.elim _ _,
      fun _ y => ⟨y, Subsingleton.elim _ _⟩⟩
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have ha : 2 ≤ Nat.card A := by
    let : Fintype A := Fintype.ofFinite A
    have hh := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial A)
    rw [Nat.card_eq_fintype_card]
    omega
  by_cases hd : d = 0
  · subst d
    let : Fintype ((Fin 0 → ℤ) → A) := Fintype.ofFinite _
    have he : Preinjective S φ ↔ Injective (localMap S φ) := by
      constructor
      · intro hp x y hi
        exact hp x y (Set.toFinite _) hi
      · intro hi x y _ heq
        exact hi heq
    exact (Finite.injective_iff_surjective (f := localMap S φ)).symm.trans he.symm
  by_cases hd1 : d = 1
  · subst d
    exact rank_one_from_native S φ
  constructor
  · intro hs x y hf hi
    by_contra hne
    obtain ⟨c, hc, N, hN⟩ := strict_image_box_loss d (by omega) S φ ha x y hf hi hne
    have hh := hN N le_rfl
    dsimp only [imagePatternCount] at hh
    rw [surjective_patterns_full S φ hs, card_box, Nat.cast_pow, Real.log_pow,
      Nat.cast_pow] at hh
    have hv : ((N + 1 : ℕ) : ℝ) ^ d ≠ 0 := by positivity
    rw [mul_div_cancel_left₀ _ hv] at hh
    exact (not_le_of_gt hc) hh
  · exact surjective_of_preinjective d S φ ha

end D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
