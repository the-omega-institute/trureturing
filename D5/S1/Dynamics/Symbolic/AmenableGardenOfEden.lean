/- GID: D5/S1/Dynamics/Symbolic/AmenableGardenOfEden
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/AmenableGardenOfEden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite collars and actual image patterns for group cellular maps. -/

import D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
import Mathlib.MeasureTheory.Group.FoelnerFilter
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Action.Opposite

/-! Finite-pattern arguments for full shifts on arbitrary groups. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

open Set Function
open scoped Pointwise

universe u v

variable {G : Type v} [Group G] {A : Type u}

/-- The full cellular map with right-multiplied neighborhood coordinates. -/
def localMap (S : Finset G) (φ : (S → A) → A) (x : G → A) : G → A :=
  fun g => φ (fun s => x (g * s))

/-- Injectivity on configurations differing at only finitely many sites. -/
def Preinjective (S : Finset G) (φ : (S → A) → A) : Prop :=
  ∀ x y : G → A, Set.Finite {g | x g ≠ y g} → localMap S φ x = localMap S φ y → x = y

/-- Joint restrictions of one complete cellular image. -/
def ImagePatterns (S : Finset G) (φ : (S → A) → A) (F : Finset G) :=
  Set.range (fun x : G → A => fun f : F => localMap S φ x f)

/-- Replace the pattern on the left translate `t*C`, retaining its complement. -/
def writePattern (C : Finset G) (p : C → A) (t : G) (x : G → A) : G → A := by
  classical
  exact fun g => if h : t⁻¹ * g ∈ C then p ⟨t⁻¹ * g, h⟩ else x g

private def collar (D S : Finset G) : Finset G := by
  classical
  exact D ∪ D.biUnion (fun a => S.biUnion (fun s => S.image (fun r => a * s⁻¹ * r)))

private theorem mem_collar_core (D S : Finset G) {a : G} (ha : a ∈ D) :
    a ∈ collar D S := by
  classical
  exact Finset.mem_union_left _ ha

private theorem mem_collar_window (D S : Finset G) {a s r : G}
    (ha : a ∈ D) (hs : s ∈ S) (hr : r ∈ S) : a * s⁻¹ * r ∈ collar D S := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨a, ha, Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩⟩)

private theorem localMap_piecewise_of_collar (D S : Finset G) (φ : (S → A) → A)
    {x y z : G → A} (hout : ∀ a, a ∉ D → x a = y a)
    (himage : localMap S φ x = localMap S φ y)
    (hz : ∀ a ∈ collar D S, z a = x a) :
    localMap S φ ((↑(collar D S) : Set G).piecewise y z) = localMap S φ z := by
  classical
  funext a
  by_cases htouch : ∃ s : S, a * s ∈ D
  · obtain ⟨s, hs⟩ := htouch
    have hwindow (r : S) : a * r ∈ collar D S := by
      simpa only [mul_inv_cancel_right] using mem_collar_window D S hs s.property r.property
    change φ (fun r : S => (↑(collar D S) : Set G).piecewise y z (a * r)) =
      φ (fun r : S => z (a * r))
    have hp : (fun r : S => (↑(collar D S) : Set G).piecewise y z (a * r)) =
        (fun r : S => y (a * r)) := by
      funext r
      exact Set.piecewise_eq_of_mem _ _ _ (hwindow r)
    have he : (fun r : S => z (a * r)) = (fun r : S => x (a * r)) :=
      funext (fun r => hz _ (hwindow r))
    rw [hp, he]
    exact (congrFun himage a).symm
  · apply congrArg φ
    funext r
    change (↑(collar D S) : Set G).piecewise y z (a * r) = z (a * r)
    by_cases hc : a * r ∈ collar D S
    · rw [Set.piecewise_eq_of_mem _ _ _ hc]
      exact (hout _ (fun hd => htouch ⟨r, hd⟩)).symm.trans (hz _ hc).symm
    · exact Set.piecewise_eq_of_notMem _ _ _ hc

private theorem writePattern_at (C : Finset G) (p : C → A) (t : G) (x : G → A)
    (c : C) : writePattern C p t x (t * c) = p c := by
  classical
  simp only [writePattern, inv_mul_cancel_left]
  exact dite_eq_left c.property

private theorem exists_erasable_shape (S : Finset G) (φ : (S → A) → A)
    {x y : G → A} (hf : Set.Finite {a | x a ≠ y a})
    (hi : localMap S φ x = localMap S φ y) (hne : x ≠ y) :
    ∃ C : Finset G, ∃ p q : C → A, p ≠ q ∧
      ∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
        localMap S φ (writePattern C q t z) = localMap S φ z := by
  classical
  let D := hf.toFinset
  let C := collar D S
  let p : C → A := fun c => x c
  let q : C → A := fun c => y c
  have hout (a : G) (ha : a ∉ D) : x a = y a := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using ha
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have haD : a ∈ D := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
  have haC : a ∈ C := mem_collar_core D S haD
  refine ⟨C, p, q, (fun he => ha (congrFun he ⟨a, haC⟩)), ?_⟩
  intro t z hz
  let z' : G → A := fun b => z (t * b)
  have hz' : ∀ b ∈ collar D S, z' b = x b := fun b hb => hz ⟨b, hb⟩
  have he := localMap_piecewise_of_collar D S φ hout hi hz'
  funext b
  have he' := congrFun he (t⁻¹ * b)
  change φ (fun s : S => (↑C : Set G).piecewise y z' (t⁻¹ * b * s)) =
    φ (fun s : S => z' (t⁻¹ * b * s)) at he'
  have hw : (fun s : S => writePattern C q t z (b * s)) =
      (fun s : S => (↑C : Set G).piecewise y z' (t⁻¹ * b * s)) := by
    funext s
    dsimp only [writePattern]
    rw [← mul_assoc]
    split_ifs with hc
    · exact (Set.piecewise_eq_of_mem _ _ _ hc).symm
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc]
      simp only [z', mul_assoc, mul_inv_cancel_left]
  change φ (fun s : S => writePattern C q t z (b * s)) = φ (fun s : S => z (b * s))
  rw [hw, he']
  congr 1
  funext s
  simp only [z', mul_assoc, mul_inv_cancel_left]

private theorem erase_disjoint_patterns (S : Finset G) (φ : (S → A) → A)
    (C : Finset G) (p q : C → A) (hpq : p ≠ q)
    (herase : ∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
      localMap S φ (writePattern C q t z) = localMap S φ z)
    (T : Finset G)
    (hdis : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e)
    (x : G → A) :
    ∃ y : G → A, localMap S φ y = localMap S φ x ∧
      ∀ t ∈ T, (fun c : C => y (t * c)) ≠ p := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨x, rfl, by simp⟩
  | @insert t T ht ih =>
    obtain ⟨y, hy, hay⟩ := ih (fun u hu v hv huv =>
      hdis u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv)
    by_cases hc : (fun c : C => y (t * c)) = p
    · refine ⟨writePattern C q t y, (herase t y (fun c => congrFun hc c)).trans hy, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simpa only [writePattern_at] using hpq.symm
      · have heq : (fun c : C => writePattern C q t y (u * c)) =
            (fun c : C => y (u * c)) := by
          funext c
          apply dite_eq_right
          intro hh
          have hn := hdis t (Finset.mem_insert_self _ _) u (Finset.mem_insert_of_mem hu)
            (fun he => ht (he ▸ hu)) ⟨t⁻¹ * (u * c), hh⟩ c
          exact hn (mul_inv_cancel_left t (u * c))
        rw [heq]
        exact hay u hu
    · exact ⟨y, hy, fun u hu => by
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hc
        · exact hay u hu⟩

private theorem exists_dense_packing (C F : Finset G) (hC : C.Nonempty) :
    ∃ T : Finset G, T ⊆ F ∧
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e) ∧
      F.card ≤ T.card * C.card ^ 2 := by
  classical
  let good (T : Finset G) :=
    ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e
  let candidates := F.powerset.filter good
  have he : (∅ : Finset G) ∈ candidates := by simp [candidates, good]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅, he⟩
  have hsub : T ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hgood : good T := (Finset.mem_filter.mp hT).2
  have hcover (f : F) : ∃ t : T, ∃ c e : C, (f : G) * c = (t : G) * e := by
    by_contra hn
    have hn' : ∀ t : T, ∀ c e : C, (f : G) * c ≠ (t : G) * e := by
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
    have hfg : (f : G) * c f = (g : G) * c f := by
      calc
        _ = (t f : G) * e f := hkey f
        _ = (t g : G) * e g := by rw [ht, he]
        _ = (g : G) * c g := (hkey g).symm
        _ = _ := by rw [hc]
    exact mul_right_cancel hfg
  refine ⟨T, hsub, hgood, ?_⟩
  have hcard := Nat.card_le_card_of_injective key hk
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod, pow_two,
    Nat.mul_assoc] using hcard

private theorem cardinal_bound_of_disjoint_avoidance [Finite A]
    {O : Type*} (U C T : Finset G) (p : C → A) (norm : O → G → A)
    (hdis : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e)
    (hinside : ∀ t ∈ T, ∀ c ∈ C, t * c ∈ U)
    (havoid : ∀ o t, t ∈ T → (fun c : C => norm o (t * c)) ≠ p)
    (hdet : ∀ o o', (∀ a ∈ U, norm o a = norm o' a) → o = o') :
    Nat.card O ≤ (Nat.card A ^ C.card - 1) ^ T.card *
      Nat.card A ^ (U.card - T.card * C.card) ∧ T.card * C.card ≤ U.card := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let B := {w : C → A // w ≠ p}
  let K := T.biUnion (fun t => C.image (fun c => t * c))
  let R := U \ K
  have hKU : K ⊆ U := by
    intro a ha
    obtain ⟨t, ht, hm⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    exact hinside t ht b hb
  have hK : K.card = T.card * C.card := by
    have hd : (↑T : Set G).PairwiseDisjoint (fun t => C.image (fun c => t * c)) := by
      intro t ht u hu htu
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      obtain ⟨e, he, hea⟩ := Finset.mem_image.mp hb
      exact hdis t ht u hu htu ⟨c, hc⟩ ⟨e, he⟩ (hca.trans hea.symm)
    dsimp only [K]
    rw [Finset.card_biUnion hd]
    simp only [Finset.card_image_of_injective _ (mul_right_injective _),
      Finset.sum_const, smul_eq_mul]
  let key : O → (T → B) × (R → A) := fun o =>
    (fun t => ⟨fun c => norm o (t * c), havoid o t t.property⟩,
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

private theorem collision_image_bound [Finite A]
    (S : Finset G) (φ : (S → A) → A) (C : Finset G) (p q : C → A) (hpq : p ≠ q)
    (herase : ∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
      localMap S φ (writePattern C q t z) = localMap S φ z) (F : Finset G) :
    ∃ T : Finset G, T ⊆ F ∧
      (∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e) ∧
      F.card ≤ T.card * C.card ^ 2 ∧
      T.card * C.card ≤ (F * insert 1 (S ∪ C)).card ∧
      Nat.card (ImagePatterns S φ F) ≤ (Nat.card A ^ C.card - 1) ^ T.card *
        Nat.card A ^ ((F * insert 1 (S ∪ C)).card - T.card * C.card) := by
  classical
  obtain ⟨c, _⟩ := Function.ne_iff.mp hpq
  obtain ⟨T, hTF, hdis, hdense⟩ := exists_dense_packing C F ⟨c, c.property⟩
  let source (o : ImagePatterns S φ F) : G → A := Classical.choose o.property
  have hs (o : ImagePatterns S φ F) (f : F) : localMap S φ (source o) f = o.val f :=
    congrFun (Classical.choose_spec o.property) f
  have hn (o : ImagePatterns S φ F) :=
    erase_disjoint_patterns S φ C p q hpq herase T hdis (source o)
  choose norm hnorm havoid using hn
  have hinside : ∀ t ∈ T, ∀ c ∈ C, t * c ∈ F * insert 1 (S ∪ C) := by
    intro t ht c hc
    exact Finset.mul_mem_mul (hTF ht)
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ hc))
  have hdet (o o' : ImagePatterns S φ F)
      (he : ∀ a ∈ F * insert 1 (S ∪ C), norm o a = norm o' a) : o = o' := by
    apply Subtype.ext
    funext f
    calc
      o.val f = localMap S φ (norm o) f := ((congrFun (hnorm o) f).trans (hs o f)).symm
      _ = localMap S φ (norm o') f := by
        apply congrArg φ
        funext s
        exact he _ (Finset.mul_mem_mul f.property
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ s.property)))
      _ = o'.val f := (congrFun (hnorm o') f).trans (hs o' f)
  have hc := cardinal_bound_of_disjoint_avoidance
    (F * insert 1 (S ∪ C)) C T p norm hdis hinside havoid hdet
  exact ⟨T, hTF, hdis, hdense, hc.2, hc.1⟩

/-- A finite collision supplies uniform complete-image-preserving replacements and
simultaneous packing and joint-image counting bounds on every finite shape. -/
theorem collision_replacement_count [Finite A]
    (S : Finset G) (φ : (S → A) → A) {x y : G → A}
    (hne : x ≠ y) (hf : Set.Finite {g | x g ≠ y g})
    (hi : localMap S φ x = localMap S φ y) :
    ∃ C : Finset G, ∃ p q : C → A, p ≠ q ∧
      (∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
        localMap S φ (writePattern C q t z) = localMap S φ z) ∧
      ∀ F : Finset G, ∃ T : Finset G, T ⊆ F ∧
        (∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ c : C, ∀ e : C, t * c ≠ u * e) ∧
        F.card ≤ T.card * C.card ^ 2 ∧
        T.card * C.card ≤ (F * insert 1 (S ∪ C)).card ∧
        Nat.card (ImagePatterns S φ F) ≤ (Nat.card A ^ C.card - 1) ^ T.card *
          Nat.card A ^ ((F * insert 1 (S ∪ C)).card - T.card * C.card) := by
  classical
  obtain ⟨C, p, q, hpq, herase⟩ := exists_erasable_shape S φ hf hi hne
  exact ⟨C, p, q, hpq, herase, collision_image_bound S φ C p q hpq herase⟩

end D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
