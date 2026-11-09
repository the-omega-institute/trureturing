/- GID: D5/S1/Dynamics/Symbolic/AmenableGardenOfEden
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/AmenableGardenOfEden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moore-Myhill for full cellular maps on discrete amenable groups. -/

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

def collar (D S : Finset G) : Finset G := by
  classical
  exact D ∪ D.biUnion (fun a => S.biUnion (fun s => S.image (fun r => a * s⁻¹ * r)))

theorem mem_collar_core (D S : Finset G) {a : G} (ha : a ∈ D) :
    a ∈ collar D S := by
  classical
  exact Finset.mem_union_left _ ha

private theorem mem_collar_window (D S : Finset G) {a s r : G}
    (ha : a ∈ D) (hs : s ∈ S) (hr : r ∈ S) : a * s⁻¹ * r ∈ collar D S := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨a, ha, Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩⟩)

theorem localMap_piecewise_of_collar (D S : Finset G) (φ : (S → A) → A)
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

theorem exists_dense_packing (C F : Finset G) (hC : C.Nonempty) :
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

open Filter Topology MeasureTheory
open scoped symmDiff ENNReal

private theorem mul_card_le_boundary (F E : Finset G) :
    (F * E).card ≤ F.card + ∑ e ∈ E, ((F.image (fun f => f * e)) ∆ F).card := by
  classical
  have hd : (F * E) \ F = E.biUnion (fun e => (F.image (fun f => f * e)) \ F) := by
    ext a
    simp only [Finset.mem_mul, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_image]
    aesop
  calc
    (F * E).card ≤ ((F * E) \ F).card + F.card := Finset.card_le_card_sdiff_add_card
    _ = (E.biUnion (fun e => (F.image (fun f => f * e)) \ F)).card + F.card := by rw [hd]
    _ ≤ (∑ e ∈ E, ((F.image (fun f => f * e)) \ F).card) + F.card :=
      Nat.add_le_add_right Finset.card_biUnion_le _
    _ ≤ F.card + ∑ e ∈ E, ((F.image (fun f => f * e)) ∆ F).card := by
      rw [Nat.add_comm]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun e _ =>
        Finset.card_le_card Finset.symmDiff_subset_sdiff)) _

theorem mul_ratio_tendsto {ι : Type*} {l : Filter ι} (F : ι → Finset G)
    (hpos : ∀ᶠ i in l, (F i).Nonempty)
    (hboundary : ∀ e : G, Tendsto
      (fun i => (((F i).image (fun f => f * e) ∆ F i).card : ℝ) / (F i).card) l (𝓝 0))
    (E : Finset G) (hE : 1 ∈ E) :
    Tendsto (fun i => ((F i * E).card : ℝ) / (F i).card) l (𝓝 1) := by
  classical
  let boundary (i : ι) := ∑ e ∈ E,
    (((F i).image (fun f => f * e) ∆ F i).card : ℝ) / (F i).card
  have hb : Tendsto boundary l (𝓝 0) := by
    simpa only [Finset.sum_const_zero, boundary] using
      tendsto_finsetSum E (fun e _ => hboundary e)
  have hl : ∀ᶠ i in l, 0 ≤ ((F i * E).card : ℝ) / (F i).card - 1 := by
    filter_upwards [hpos] with i hi
    have hsub : F i ⊆ F i * E := by
      intro a ha
      simpa only [mul_one] using Finset.mul_mem_mul ha hE
    have hc : ((F i).card : ℝ) ≤ (F i * E).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hp : (0 : ℝ) < (F i).card := by exact_mod_cast hi.card_pos
    rw [sub_nonneg, le_div_iff₀ hp, one_mul]
    exact hc
  have hu : ∀ᶠ i in l, ((F i * E).card : ℝ) / (F i).card - 1 ≤ boundary i := by
    filter_upwards [hpos] with i hi
    have hc := (Nat.cast_le (α := ℝ)).mpr (mul_card_le_boundary (F i) E)
    simp only [Nat.cast_add, Nat.cast_sum] at hc
    have hp : (0 : ℝ) < (F i).card := by exact_mod_cast hi.card_pos
    have hh := div_le_div_of_nonneg_right hc hp.le
    rw [add_div, div_self hp.ne'] at hh
    dsimp only [boundary]
    rw [← Finset.sum_div]
    linarith
  have hzero := squeeze_zero' hl hu hb
  convert hzero.add_const 1 using 1 <;> simp

def finiteShape (s : Set G) : Finset G :=
  if h : s.Finite then h.toFinset else ∅

theorem maximal_shapes [MeasurableSpace G] [MeasurableSingletonClass G] :
    (∀ᶠ s in maxFoelner Gᵐᵒᵖ (Measure.count : Measure G), (finiteShape s).Nonempty) ∧
    ∀ e : G, Tendsto (fun s : Set G =>
      (((finiteShape s).image (fun f => f * e) ∆ finiteShape s).card : ℝ) /
        (finiteShape s).card)
      (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)) (𝓝 0) := by
  classical
  have hfoel := isFoelner_maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)
  have hfin : ∀ᶠ s in maxFoelner Gᵐᵒᵖ (Measure.count : Measure G), s.Finite := by
    filter_upwards [hfoel.eventually_meas_ne_top] with s hs
    exact Measure.count_apply_lt_top.mp (lt_top_iff_ne_top.mpr hs)
  have hcoe (s : Set G) (hs : s.Finite) : (↑(finiteShape s) : Set G) = s := by
    simp only [finiteShape, dite_eq_left hs, Set.Finite.coe_toFinset]
  refine ⟨?_, ?_⟩
  · filter_upwards [hfin, hfoel.eventually_meas_ne_zero] with s hs hn
    have hn' := Measure.count_ne_zero_iff.mp hn
    rw [← hcoe s hs] at hn'
    exact Finset.coe_nonempty.mp hn'
  · intro e
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
      (hfoel.tendsto_meas_smul_symmDiff (MulOpposite.op e))
    simp only [ENNReal.toReal_zero] at ht
    apply ht.congr'
    filter_upwards [hfin] with s hs
    have he : MulOpposite.op e • (↑(finiteShape s) : Set G) =
        (↑((finiteShape s).image (fun f => f * e)) : Set G) := by
      change (fun f => f * e) '' (↑(finiteShape s) : Set G) = _
      exact Finset.coe_image.symm
    change (Measure.count ((MulOpposite.op e • s) ∆ s) / Measure.count s).toReal = _
    conv_lhs => rw [← hcoe s hs]
    rw [he, ← Finset.coe_symmDiff, Measure.count_apply_finset,
      Measure.count_apply_finset, ENNReal.toReal_div]
    simp

private theorem missing_pattern_of_not_surjective [Finite A]
    (S : Finset G) (φ : (S → A) → A) (hns : ¬ Surjective (localMap S φ)) :
    ∃ C : Finset G, C.Nonempty ∧ ∃ p : C → A,
      ∀ (x : G → A) (t : G), (fun c : C => localMap S φ x (t * c)) ≠ p := by
  classical
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hcont : Continuous (localMap S φ) := by
    apply continuous_pi
    intro z
    exact continuous_of_discreteTopology.comp (continuous_pi (fun s : S =>
      continuous_apply (z * s)))
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
  let x' : G → A := fun a => x (t * a)
  have hm : localMap S φ x' ∈ (↑C : Set G).pi U := by
    intro c hc
    have he' := congrFun he ⟨c, hc⟩
    have hshift : localMap S φ x' c = localMap S φ x (t * c) := by
      simp only [localMap, x', mul_assoc]
    rw [hshift, he']
    exact (hU c hc).2
  exact hsub hm ⟨x', rfl⟩

private theorem missing_image_bound [Finite A]
    (S : Finset G) (φ : (S → A) → A) (C : Finset G) (hC : C.Nonempty) (p : C → A)
    (hmissing : ∀ (x : G → A) (t : G), (fun c : C => localMap S φ x (t * c)) ≠ p)
    (F B U : Finset G) (hFU : F ⊆ U) (hin : ∀ t ∈ B, ∀ c ∈ C, t * c ∈ U) :
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
      Nat.card (ImagePatterns S φ ((F * insert 1 (S.image (fun s => s⁻¹))))) := by
  classical
  let a : A := Classical.choice ‹Nonempty A›
  let lift (w : F → A) : G → A := fun z => if hz : z ∈ F then w ⟨z, hz⟩ else a
  let E := insert 1 (S.image (fun s => s⁻¹))
  let key : (F → A) → ImagePatterns S φ ((F * E)) := fun w =>
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
      by_cases hz : z ∈ (F * E)
      · exact congrFun (congrArg Subtype.val he) ⟨z, hz⟩
      · apply congrArg φ
        funext s
        have hout : z * (s : G) ∉ F := by
          intro hin
          have hneg : (s : G)⁻¹ ∈ E := Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨(s : G), s.property, rfl⟩)
          have hm := Finset.mul_mem_mul hin hneg
          exact hz (by simpa only [mul_inv_cancel_right] using hm)
        simp only [lift, dite_eq_right hout]
    have hinput := hp (lift w) (lift v) hf hi
    funext z
    have hh := congrFun hinput z
    simpa only [lift, dite_eq_left z.property] using hh
  have hc := Nat.card_le_card_of_injective key hk
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

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

private theorem packing_limit_contradiction {ι : Type*} {l : Filter ι} [NeBot l]
    {a b : ℕ} (ha : 2 ≤ a) (hb : 0 < b) (vol size count tiles : ι → ℕ)
    (hdata : ∀ᶠ i in l, 0 < vol i ∧ a ^ vol i ≤ count i ∧
      vol i ≤ tiles i * b ^ 2 ∧ tiles i * b ≤ size i ∧
      count i ≤ (a ^ b - 1) ^ tiles i * a ^ (size i - tiles i * b))
    (hratio : Tendsto (fun i => (size i : ℝ) / vol i) l (𝓝 1)) : False := by
  let δ := ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2
  have hbound : ∀ᶠ i in l, 0 < δ ∧ Real.log (a : ℝ) ≤
      (size i : ℝ) / vol i * Real.log (a : ℝ) - δ := by
    filter_upwards [hdata] with i hi
    obtain ⟨hv, hlower, hdense, hinside, hcount⟩ := hi
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have hf : 0 < count i := lt_of_lt_of_le (pow_pos (by omega : 0 < a) _) hlower
    have hh := LatticeGardenOfEden.logarithmic_packing_bound ha hb hv hf hdense hinside hcount
    have hloglower : Real.log (a : ℝ) ≤ Real.log (count i : ℝ) / vol i := by
      have hc : (a : ℝ) ^ vol i ≤ (count i : ℝ) := by exact_mod_cast hlower
      have hlog := Real.log_le_log (pow_pos ha0 _) hc
      rw [Real.log_pow] at hlog
      apply (le_div_iff₀ (by exact_mod_cast hv : (0 : ℝ) < vol i)).mpr
      simpa only [mul_comm] using hlog
    exact ⟨hh.1, hloglower.trans hh.2⟩
  obtain ⟨i, hi⟩ := hbound.exists
  have hδ : 0 < δ := hi.1
  have hlim : Tendsto (fun i => (size i : ℝ) / vol i * Real.log (a : ℝ) - δ)
      l (𝓝 (Real.log (a : ℝ) - δ)) := by
    simpa only [one_mul] using (hratio.mul_const (Real.log (a : ℝ))).sub_const δ
  have hle : Real.log (a : ℝ) ≤ Real.log (a : ℝ) - δ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hbound.mono (fun _ hi => hi.2))
  linarith

private theorem preinjective_of_surjective [Finite A] [Nonempty A]
    {ι : Type*} {l : Filter ι} [NeBot l] (F : ι → Finset G)
    (hpos : ∀ᶠ i in l, (F i).Nonempty)
    (hboundary : ∀ e : G, Tendsto
      (fun i => (((F i).image (fun f => f * e) ∆ F i).card : ℝ) / (F i).card) l (𝓝 0))
    (S : Finset G) (φ : (S → A) → A) (ha : 2 ≤ Nat.card A)
    (hs : Surjective (localMap S φ)) : Preinjective S φ := by
  classical
  intro x y hf hi
  by_contra hne
  obtain ⟨C, p, q, hpq, _herase, hpack⟩ := collision_replacement_count S φ hne hf hi
  obtain ⟨c, _⟩ := Function.ne_iff.mp hpq
  have hb : 0 < C.card := Finset.card_pos.mpr ⟨c, c.property⟩
  choose T _hsub _hdis hdense hinside hcount using fun i => hpack (F i)
  apply packing_limit_contradiction (l := l) ha hb (fun i => (F i).card)
    (fun i => (F i * insert 1 (S ∪ C)).card)
    (fun i => Nat.card (ImagePatterns S φ (F i))) (fun i => (T i).card)
  · filter_upwards [hpos] with i hi
    exact ⟨hi.card_pos, (surjective_patterns_full S φ hs (F i)).ge,
      hdense i, hinside i, hcount i⟩
  · exact mul_ratio_tendsto F hpos hboundary _ (Finset.mem_insert_self _ _)

private theorem surjective_of_preinjective [Finite A] [Nonempty A]
    {ι : Type*} {l : Filter ι} [NeBot l] (B : ι → Finset G)
    (hpos : ∀ᶠ i in l, (B i).Nonempty)
    (hboundary : ∀ e : G, Tendsto
      (fun i => (((B i).image (fun f => f * e) ∆ B i).card : ℝ) / (B i).card) l (𝓝 0))
    (S : Finset G) (φ : (S → A) → A) (ha : 2 ≤ Nat.card A)
    (hp : Preinjective S φ) : Surjective (localMap S φ) := by
  classical
  by_contra hns
  obtain ⟨C, hC, p, hmissing⟩ := missing_pattern_of_not_surjective S φ hns
  let invS := S.image (fun s => s⁻¹)
  let E0 := insert 1 invS
  let E := insert 1 (invS ∪ C)
  have hsub (i : ι) : B i * E0 ⊆ B i * E := by
    apply Finset.mul_subset_mul_left
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
  have hin (i : ι) : ∀ t ∈ B i, ∀ c ∈ C, t * c ∈ B i * E := by
    intro t ht c hc
    exact Finset.mul_mem_mul ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ hc))
  have hpack (i : ι) := missing_image_bound S φ C hC p hmissing
    (B i * E0) (B i) (B i * E) (hsub i) (hin i)
  choose T hdense hcount hinside using hpack
  apply packing_limit_contradiction (l := l) ha hC.card_pos (fun i => (B i).card)
    (fun i => (B i * E).card)
    (fun i => Nat.card (ImagePatterns S φ (B i * E0))) (fun i => (T i).card)
  · filter_upwards [hpos] with i hi
    exact ⟨hi.card_pos, preinjective_pattern_lower S φ hp (B i),
      hdense i, hinside i, hcount i⟩
  · exact mul_ratio_tendsto B hpos hboundary E (Finset.mem_insert_self _ _)

/-- Moore–Myhill for the full shift on a discrete group with a nontrivial right
counting Følner filter, including finite groups and empty alphabets. -/
theorem garden_of_eden [Finite A]
    (ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (S : Finset G) (φ : (S → A) → A) :
    Surjective (localMap S φ) ↔ Preinjective S φ := by
  classical
  by_cases hA : Subsingleton A
  · letI : Subsingleton A := hA
    exact ⟨fun _ _ _ _ _ => Subsingleton.elim _ _,
      fun _ y => ⟨y, Subsingleton.elim _ _⟩⟩
  letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have ha : 2 ≤ Nat.card A := by
    letI : Fintype A := Fintype.ofFinite A
    have hh := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial A)
    rw [Nat.card_eq_fintype_card]
    omega
  letI : MeasurableSpace G := ⊤
  letI : NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)) := ham
  obtain ⟨hpos, hboundary⟩ := maximal_shapes (G := G)
  exact ⟨preinjective_of_surjective finiteShape hpos hboundary S φ ha,
    surjective_of_preinjective finiteShape hpos hboundary S φ ha⟩

end D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
