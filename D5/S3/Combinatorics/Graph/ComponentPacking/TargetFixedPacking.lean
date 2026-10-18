/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/TargetFixedPacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/TargetFixedPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/ComponentPacking/IntegerLineComponents]
   utility: none
   digest: The shortest ordered prefix gives an injective target-fixed component translation. -/

module

public import D5.S3.Combinatorics.Graph.ComponentPacking.IntegerLineComponents

/-! Ordered component translations preserving every specified directed edge. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ComponentPacking

open scoped BigOperators

/-- An initial segment in the original order of component minima. -/
def OrderedPrefix (A L : Finset ℤ) : Prop :=
  L ⊆ A ∧ ∀ a ∈ L, ∀ b ∈ A, b < a → b ∈ L

/-- Small families go entirely right; otherwise use the shortest prefix whose
vertex sum reaches the number of detached components minus one. -/
def ShortestPrefix (A : Finset ℤ) (size : ℤ → ℤ) (L : Finset ℤ) : Prop :=
  OrderedPrefix A L ∧
    (A.card ≤ 1 → L = ∅) ∧
    (2 ≤ A.card → (A.card : ℤ) - 1 ≤ ∑ a ∈ L, size a) ∧
    (2 ≤ A.card → ∀ P : Finset ℤ, OrderedPrefix A P →
      (A.card : ℤ) - 1 ≤ ∑ a ∈ P, size a → L.card ≤ P.card)

private theorem shortest_prefix_split (A : Finset ℤ) (ell : ℤ → ℤ)
    (positive : ∀ a ∈ A, 1 ≤ ell a) :
    ∃ L : Finset ℤ, ShortestPrefix A (fun a => ell a + 1) L ∧
      (∑ a ∈ L, (ell a + 1)) ≤ ∑ a ∈ A, ell a ∧
      (∑ a ∈ A \ L, (ell a + 1)) ≤ (∑ a ∈ A, ell a) + 1 := by
  classical
  let d := ∑ a ∈ A, ell a
  let size := fun a => ell a + 1
  have dnonneg : 0 ≤ d := Finset.sum_nonneg (fun a ha => by have := positive a ha; omega)
  have total : (∑ a ∈ A, size a) = d + A.card := by
    simp [size, d, Finset.sum_add_distrib]
  by_cases small : A.card ≤ 1
  · refine ⟨∅, ⟨⟨by simp, by simp⟩, fun _ => rfl, ?_, ?_⟩, ?_, ?_⟩
    · intro h; omega
    · intro h; omega
    · simpa using dnonneg
    · simpa only [Finset.sdiff_empty] using (show (∑ a ∈ A, size a) ≤ d + 1 by
        rw [total]; omega)
  have large : 2 ≤ A.card := by omega
  have item_bound (a : ℤ) (ha : a ∈ A) : size a + ((A.card : ℤ) - 1) ≤ d + 1 := by
    have lower : (A.card : ℤ) - 1 ≤ ∑ b ∈ A.erase a, ell b := by
      calc
        (A.card : ℤ) - 1 = ∑ _b ∈ A.erase a, (1 : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem ha]
          have := Finset.card_pos.mpr ⟨a, ha⟩
          omega
        _ ≤ _ := Finset.sum_le_sum (fun b hb => positive b (Finset.mem_of_mem_erase hb))
    have split := Finset.sum_erase_add A ell ha
    change (∑ b ∈ A.erase a, ell b) + ell a = d at split
    dsimp only [size]
    omega
  let candidates := A.powerset.filter (fun L =>
    OrderedPrefix A L ∧ (A.card : ℤ) - 1 ≤ ∑ a ∈ L, size a)
  have feasible : candidates.Nonempty := by
    refine ⟨A, Finset.mem_filter.mpr ⟨by simp, ⟨?_, ?_⟩⟩⟩
    · exact ⟨(fun _ h => h), fun _ _ _ hb _ => hb⟩
    · rw [total]; omega
  obtain ⟨L, hL, minimal⟩ := Finset.exists_min_image candidates Finset.card feasible
  obtain ⟨hprefix, threshold⟩ := (Finset.mem_filter.mp hL).2
  have nonempty : L.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at threshold
    omega
  let a := L.max' nonempty
  have ha : a ∈ L := Finset.max'_mem _ _
  have prevPrefix : OrderedPrefix A (L.erase a) := by
    refine ⟨(Finset.erase_subset _ _).trans hprefix.1, ?_⟩
    intro b hb c hc hcb
    have hba : b ≤ a := Finset.le_max' _ _ (Finset.mem_of_mem_erase hb)
    exact Finset.mem_erase.mpr ⟨by omega,
      hprefix.2 b (Finset.mem_of_mem_erase hb) c hc hcb⟩
  have below : (∑ b ∈ L.erase a, size b) < (A.card : ℤ) - 1 := by
    by_contra h
    have admissible : L.erase a ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr prevPrefix.1, prevPrefix, by omega⟩
    have := minimal _ admissible
    have := Finset.card_erase_lt_of_mem ha
    omega
  have splitL := Finset.sum_erase_add L size ha
  have bounda := item_bound a (hprefix.1 ha)
  have upper : (∑ a ∈ L, size a) ≤ d := by omega
  have complement := Finset.sum_sdiff hprefix.1 (f := size)
  rw [total] at complement
  refine ⟨L, ⟨hprefix, by omega, fun _ => threshold, ?_⟩, upper, ?_⟩
  · intro _ P hp hsum
    exact minimal P (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hp.1, hp, hsum⟩)
  · change (∑ a ∈ A \ L, size a) ≤ d + 1
    omega

/-- Sum of vertex sizes strictly before the component with minimum `a`. -/
noncomputable def precedingSize (A : Finset ℤ) (size : ℤ → ℤ) (a : ℤ) : ℤ := by
  classical
  exact ∑ b ∈ A.filter (fun b => b < a), size b

private theorem preceding_nonneg (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) : 0 ≤ precedingSize A size a := by
  classical
  exact Finset.sum_nonneg (fun b hb => hs b (Finset.mem_filter.mp hb).1)

private theorem preceding_add_le (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) (ha : a ∈ A) :
    precedingSize A size a + size a ≤ ∑ b ∈ A, size b := by
  classical
  have hnot : a ∉ A.filter (fun b => b < a) := by simp
  rw [precedingSize, add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.insert_subset ha (Finset.filter_subset _ _)) (fun b hb _ => hs b hb)

private theorem preceding_strict_step (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) (ha : a ∈ A) (b : ℤ) (hab : a < b) :
    precedingSize A size a + size a ≤ precedingSize A size b := by
  classical
  have hnot : a ∉ A.filter (fun c => c < a) := by simp
  have sub : insert a (A.filter (fun c => c < a)) ⊆ A.filter (fun c => c < b) := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_filter.mpr ⟨ha, hab⟩
    · obtain ⟨hcA, hca⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hcA, by omega⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg sub
    (fun c hc _ => hs c (Finset.mem_filter.mp hc).1)
  simpa only [Finset.sum_insert hnot, precedingSize, add_comm] using this

/-- The complete specified construction, including the original-order shortest
prefix, the translation formula, and guarantees on the entire occupied domain. -/
structure CanonicalTargetPacking (E : Finset ℤ) (q : ℤ) where
  intervals : IntegerLineIntervals E q
  left : Finset ℤ
  split : ShortestPrefix (intervals.roots.erase intervals.target)
    (fun a => intervals.right a - a + 1) left
  map : ℤ → ℤ
  formula : ∀ a ∈ intervals.roots, ∀ v : ℤ,
    a ≤ v → v ≤ intervals.right a →
    map v = v + (if a = intervals.target then 0 else
      if a ∈ left then intervals.target - (∑ b ∈ left, (intervals.right b - b + 1)) +
        precedingSize left (fun b => intervals.right b - b + 1) a - a
      else intervals.right intervals.target + 1 +
        precedingSize (intervals.roots.erase intervals.target \ left)
          (fun b => intervals.right b - b + 1) a - a)
  injective : Set.InjOn map (↑(occupiedVertices E q))
  fixed_target : ∀ v : ℤ, intervals.target ≤ v →
    v ≤ intervals.right intervals.target → map v = v
  translates : ∀ a ∈ intervals.roots, ∃ c : ℤ,
    ∀ v : ℤ, a ≤ v → v ≤ intervals.right a → map v = v + c
  edge_preserving : ∀ e ∈ E, map (e + 1) = map e + 1
  edge_bounds : ∀ e ∈ E, q - (E.card : ℤ) ≤ map e ∧ map e ≤ q + (E.card : ℤ)

/-- The ordered shortest-prefix construction fixes the whole target component,
is injective on all occupied vertices, and bounds every queried left endpoint. -/
theorem canonical_target_fixed_packing (E : Finset ℤ) (q : ℤ) :
    Nonempty (CanonicalTargetPacking E q) := by
  classical
  let D := Classical.choice (integer_line_component_intervals E q)
  let ell : ℤ → ℤ := fun a => D.right a - a
  let size : ℤ → ℤ := fun a => ell a + 1
  let A := D.roots.erase D.target
  have positive (a : ℤ) (ha : a ∈ A) : 1 ≤ ell a := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ha
    have := D.detached_positive a hmem hne
    dsimp only [ell]
    omega
  obtain ⟨L, hsplit, hx, hy⟩ := shortest_prefix_split A ell positive
  let R := A \ L
  let x := ∑ a ∈ L, size a
  let y := ∑ a ∈ R, size a
  let d := ∑ a ∈ A, ell a
  have subL : L ⊆ A := hsplit.1.1
  have subR : R ⊆ A := Finset.sdiff_subset
  have rootL (a : ℤ) (ha : a ∈ L) : a ∈ D.roots :=
    Finset.mem_of_mem_erase (subL ha)
  have rootR (a : ℤ) (ha : a ∈ R) : a ∈ D.roots :=
    Finset.mem_of_mem_erase (subR ha)
  have size_nonneg (a : ℤ) (ha : a ∈ D.roots) : 0 ≤ size a := by
    have := D.nonempty a ha
    dsimp only [size, ell]
    omega
  have nonnegL (a : ℤ) (ha : a ∈ L) : 0 ≤ size a := size_nonneg a (rootL a ha)
  have nonnegR (a : ℤ) (ha : a ∈ R) : 0 ≤ size a := size_nonneg a (rootR a ha)
  have xnonneg : 0 ≤ x := Finset.sum_nonneg nonnegL
  have ynonneg : 0 ≤ y := Finset.sum_nonneg nonnegR
  have dnonneg : 0 ≤ d := Finset.sum_nonneg (fun a ha => by have := positive a ha; omega)
  have allLen : (∑ a ∈ D.roots, ell a) = (E.card : ℤ) := by
    rw [← D.edge_count, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact (Int.toNat_of_nonneg (sub_nonneg.mpr (D.nonempty a ha))).symm
  have accounting : d + ell D.target = (E.card : ℤ) := by
    simpa only [allLen] using Finset.sum_erase_add D.roots ell D.target_mem
  have qlo := D.target_bounds.1
  have qhi := D.target_bounds.2
  have lenspec (a : ℤ) : ell a = D.right a - a := rfl
  have unique (a : ℤ) (ha : a ∈ D.roots) (b : ℤ) (hb : b ∈ D.roots)
      (v : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hv' : b ≤ v ∧ v ≤ D.right b) : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have := D.separated a ha b hb h; omega
    · exact h
    · have := D.separated b hb a ha h; omega
  let shift : ℤ → ℤ := fun a => if a = D.target then 0 else
    if a ∈ L then D.target - x + precedingSize L size a - a
    else D.right D.target + 1 + precedingSize R size a - a
  let f : ℤ → ℤ := fun v =>
    ∑ a ∈ D.roots, if a ≤ v ∧ v ≤ D.right a then v + shift a else 0
  have on_interval (a : ℤ) (ha : a ∈ D.roots) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) : f v = v + shift a := by
    dsimp only [f]
    rw [Finset.sum_eq_single a]
    · exact ite_eq_left hv
    · intro b hb hne
      apply ite_eq_right
      intro hbv
      exact hne (unique b hb a ha v hbv hv)
    · intro hn
      exact (hn ha).elim
  have target_shift : shift D.target = 0 := by simp [shift]
  have target_fixed (v : ℤ) (hv₁ : D.target ≤ v) (hv₂ : v ≤ D.right D.target) : f v = v := by
    simpa only [target_shift, add_zero] using on_interval _ D.target_mem v ⟨hv₁, hv₂⟩
  have left_shift (a : ℤ) (ha : a ∈ L) :
      shift a = D.target - x + precedingSize L size a - a := by
    have hne := (Finset.mem_erase.mp (subL ha)).1
    simp only [shift, ite_eq_right hne, ite_eq_left ha]
  have right_shift (a : ℤ) (ha : a ∈ R) :
      shift a = D.right D.target + 1 + precedingSize R size a - a := by
    obtain ⟨hA, hnL⟩ := Finset.mem_sdiff.mp ha
    have hne := (Finset.mem_erase.mp hA).1
    simp only [shift, ite_eq_right hne, ite_eq_right hnL]
  have left_range (a : ℤ) (ha : a ∈ L) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) : D.target - x ≤ f v ∧ f v < D.target := by
    rw [on_interval a (rootL a ha) v hv, left_shift a ha]
    have hp := preceding_nonneg L size nonnegL a
    have hb := preceding_add_le L size nonnegL a ha
    change precedingSize L size a + (D.right a - a + 1) ≤ x at hb
    omega
  have right_range (a : ℤ) (ha : a ∈ R) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) :
      D.right D.target < f v ∧ f v ≤ D.right D.target + y := by
    rw [on_interval a (rootR a ha) v hv, right_shift a ha]
    have hp := preceding_nonneg R size nonnegR a
    have hb := preceding_add_le R size nonnegR a ha
    change precedingSize R size a + (D.right a - a + 1) ≤ y at hb
    omega
  have same_left (a : ℤ) (ha : a ∈ L) (b : ℤ) (hb : b ∈ L) (hab : a < b)
      (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hw : b ≤ w ∧ w ≤ D.right b) :
      f v < f w := by
    rw [on_interval a (rootL a ha) v hv, on_interval b (rootL b hb) w hw,
      left_shift a ha, left_shift b hb]
    have h := preceding_strict_step L size nonnegL a ha b hab
    change precedingSize L size a + (D.right a - a + 1) ≤ precedingSize L size b at h
    omega
  have same_right (a : ℤ) (ha : a ∈ R) (b : ℤ) (hb : b ∈ R) (hab : a < b)
      (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hw : b ≤ w ∧ w ≤ D.right b) :
      f v < f w := by
    rw [on_interval a (rootR a ha) v hv, on_interval b (rootR b hb) w hw,
      right_shift a ha, right_shift b hb]
    have h := preceding_strict_step R size nonnegR a ha b hab
    change precedingSize R size a + (D.right a - a + 1) ≤ precedingSize R size b at h
    omega
  have category (a : ℤ) (ha : a ∈ D.roots) : a = D.target ∨ a ∈ L ∨ a ∈ R := by
    by_cases ht : a = D.target
    · exact Or.inl ht
    · by_cases hl : a ∈ L
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨ht, ha⟩, hl⟩))
  have disjoint_images (a : ℤ) (ha : a ∈ D.roots) (b : ℤ) (hb : b ∈ D.roots)
      (hne : a ≠ b) (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a)
      (hw : b ≤ w ∧ w ≤ D.right b) : f v ≠ f w := by
    rcases category a ha with rfl | hLa | hRa <;>
      rcases category b hb with rfl | hLb | hRb
    · exact (hne rfl).elim
    · rw [target_fixed v hv.1 hv.2]
      have := (left_range b hLb w hw).2
      omega
    · rw [target_fixed v hv.1 hv.2]
      have := (right_range b hRb w hw).1
      omega
    · rw [target_fixed w hw.1 hw.2]
      have := (left_range a hLa v hv).2
      omega
    · rcases lt_or_gt_of_ne hne with h | h
      · exact ne_of_lt (same_left a hLa b hLb h v w hv hw)
      · exact ne_of_gt (same_left b hLb a hLa h w v hw hv)
    · have := (left_range a hLa v hv).2
      have := (right_range b hRb w hw).1
      have := D.nonempty D.target D.target_mem
      omega
    · rw [target_fixed w hw.1 hw.2]
      have := (right_range a hRa v hv).1
      omega
    · have := (right_range a hRa v hv).1
      have := (left_range b hLb w hw).2
      have := D.nonempty D.target D.target_mem
      omega
    · rcases lt_or_gt_of_ne hne with h | h
      · exact ne_of_lt (same_right a hRa b hRb h v w hv hw)
      · exact ne_of_gt (same_right b hRb a hRa h w v hw hv)
  have injective : Set.InjOn f (↑(occupiedVertices E q)) := by
    intro v hv w hw heq
    obtain ⟨a, ha, hav⟩ := (D.vertices v).mp hv
    obtain ⟨b, hb, hbw⟩ := (D.vertices w).mp hw
    by_cases hab : a = b
    · subst b
      rw [on_interval a ha v hav, on_interval a ha w hbw] at heq
      omega
    · exact (disjoint_images a ha b hb hab v w hav hbw heq).elim
  have global_range (v : ℤ) (hv : v ∈ occupiedVertices E q) :
      q - (E.card : ℤ) ≤ f v ∧ f v ≤ q + (E.card : ℤ) + 1 := by
    obtain ⟨a, ha, hav⟩ := (D.vertices v).mp hv
    have hlen := lenspec D.target
    change x ≤ d at hx
    change y ≤ d + 1 at hy
    rcases category a ha with rfl | hLa | hRa
    · rw [target_fixed v hav.1 hav.2]
      omega
    · have := left_range a hLa v hav
      omega
    · have := right_range a hRa v hav
      omega
  have edge_preserving (e : ℤ) (he : e ∈ E) : f (e + 1) = f e + 1 := by
    obtain ⟨a, ha, hlo, hhi⟩ := (D.edges e).mp he
    rw [on_interval a ha (e + 1) ⟨by omega, by omega⟩,
      on_interval a ha e ⟨hlo, hhi.le⟩]
    omega
  have edge_bounds (e : ℤ) (he : e ∈ E) :
      q - (E.card : ℤ) ≤ f e ∧ f e ≤ q + (E.card : ℤ) := by
    have heV : e ∈ occupiedVertices E q :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
    have he1V : e + 1 ∈ occupiedVertices E q := Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    have h₁ := global_range e heV
    have h₂ := global_range (e + 1) he1V
    have h₃ := edge_preserving e he
    exact ⟨h₁.1, by omega⟩
  refine ⟨⟨D, L, hsplit, f, ?_, injective, target_fixed, ?_, edge_preserving, edge_bounds⟩⟩
  · intro a ha v hv₁ hv₂
    exact on_interval a ha v ⟨hv₁, hv₂⟩
  · intro a ha
    exact ⟨shift a, fun v hv₁ hv₂ => on_interval a ha v ⟨hv₁, hv₂⟩⟩

#print axioms canonical_target_fixed_packing

end D5.S3.Combinatorics.Graph.ComponentPacking
