/- GID: D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Minimum-order ultrametric spaces with equally many points are weakly similar, and weak similarity preserves the center size. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#452)
escape_witness: sim (minimum-order spaces whose centers correspond under a map strictly
  increasing on the center of the target admit a bijection carrying one metric to the other
  through that map; the halves below the diameter are glued by induction), dist_mem_center
  (every distance of a minimum-order space is central) and center_ncard_aux (a weak similarity
  maps the center bijectively onto the center).
proof_shape:
  distances, WeaklySimilar: definitions; consumers: center_ncard_aux, weak_of_mcd, result.
  g_zero, g_top, center_finite, center_ncard: bind-only helpers; consumers: sim, weak_of_mcd,
    result.
  dist_mem_center: content; consumer: weak_of_mcd.
  sim: content; consumer: weak_of_mcd.
  center_ncard_aux: content; consumer: center_ncard.
  weak_of_mcd: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center);
  D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry (zero_mem_center, le_max_center, split,
  nonempty_of_card, cross), made public here for reuse.
Search record (§3.1): the frozen ultrametric modules prove the minimum order, the sphere counts
  and isometry rigidity of minimum-order spaces; no D5 module or pinned Mathlib declaration
  defines weak similarity or relates it to minimum-order ultrametric spaces.
-/

import D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry

/-! # Weak similarity of minimum-order ultrametric spaces

A weak similarity between metric spaces `X` and `Y` is a bijection `Φ` together with a function
`f`, strictly increasing on the distances of `Y`, such that `d(x, y) = f (ρ(Φ x, Φ y))`. Two finite
ultrametric spaces of minimum order `2^(|C| - 1)` with equally many points are weakly similar, and
a weak similarity preserves `|C|`, finite or infinite. Hence, for `|X| = |Y| = 2^h` and `|C(X)| = h + 1`,
`|C(Y)| = h + 1` exactly when `X` and `Y` are weakly similar.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry (zero_mem_center le_max_center split
  nonempty_of_card cross)

/-- The set of distances of a metric space. -/
def distances (X : Type) [MetricSpace X] : Set ℝ := {r | ∃ a b : X, dist a b = r}

/-- A weak similarity (Dovgoshey–Rovenska, Definition 4.1): a bijection `Φ : X ≃ Y` and a
function `f`, strictly increasing on the distances of `Y`, with `d(x, y) = f (ρ(Φ x, Φ y))`. -/
def WeaklySimilar (X Y : Type) [MetricSpace X] [MetricSpace Y] : Prop :=
  ∃ Φ : X ≃ Y, ∃ f : ℝ → ℝ, StrictMonoOn f (distances Y) ∧
    ∀ x y : X, dist x y = f (dist (Φ x) (Φ y))

/-- On a minimum-order space every distance is central. -/
private theorem dist_mem_center (n : ℕ) : ∀ (X : Type) [MetricSpace X] [IsUltrametricDist X]
    [Finite X] (A : Finset ℝ), A.card = n + 1 → center X = ↑A → Nat.card X = 2 ^ n →
    ∀ a b : X, dist a b ∈ center X := by
  induction n with
  | zero =>
    intro X _ _ _ A _ _ hX a b
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.mp hX
    rw [Subsingleton.elim a b, dist_self]
    exact zero_mem_center X
  | succ n ih =>
    intro X _ _ _ A hA hcX hX a b
    have hcard : A.card = n + 2 := hA
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hmX : A.max' hne ∈ center X := by rw [hcX]; exact A.max'_mem hne
    obtain ⟨p⟩ := nonempty_of_card hX
    obtain ⟨q, hq⟩ := hmX.2 p
    obtain ⟨hbal, hcov, hdis⟩ := split X n A hcX hcard hX p q hq
    set m := A.max' hne
    have hEcard : (A.erase m).card = n + 1 := by
      rw [Finset.card_erase_of_mem (A.max'_mem hne)]; omega
    have hsub : (↑(A.erase m) : Set ℝ) ⊆ center X := by
      rw [hcX]; exact Finset.coe_subset.mpr (Finset.erase_subset _ _)
    have half : ∀ r : X, (dist p r = m ∨ dist q r = m) →
        ∀ a b : X, dist r a < m → dist r b < m → dist a b ∈ center X := by
      intro r hr a b ha hb
      obtain ⟨hrc, hrC⟩ := hbal r hr
      have := ih (UltrametricCenterMinimumOrder.inner r m) (A.erase m) hEcard hrC hrc
        ⟨a, ha⟩ ⟨b, hb⟩
      rw [hrC] at this
      exact hsub this
    by_cases ha : dist p a < m <;> by_cases hb' : dist p b < m
    · exact half p (Or.inr hq) a b ha hb'
    · rw [cross p a b (le_max_center X A hcX hne) ha hb']; exact hmX
    · rw [dist_comm, cross p b a (le_max_center X A hcX hne) hb' ha]; exact hmX
    · exact half q (Or.inl (by rw [dist_comm]; exact hq)) a b
        ((hcov a).resolve_left ha) ((hcov b).resolve_left hb')

/-- A map strictly increasing on one finite set of nonnegative reals containing `0` and sending
it onto another such set fixes `0`. -/
private theorem g_zero (A B : Set ℝ) (hA0 : (0 : ℝ) ∈ A) (hB0 : (0 : ℝ) ∈ B)
    (hAnn : ∀ a ∈ A, 0 ≤ a) (hBnn : ∀ b ∈ B, 0 ≤ b) (g : ℝ → ℝ) (hg : StrictMonoOn g B)
    (hgB : g '' B = A) : g 0 = 0 := by
  have h1 : 0 ≤ g 0 := hAnn _ (hgB ▸ Set.mem_image_of_mem g hB0)
  obtain ⟨b, hb, hgb⟩ : (0 : ℝ) ∈ g '' B := hgB ▸ hA0
  rcases lt_or_eq_of_le (hBnn b hb) with hlt | heq
  · have := hg hB0 hb hlt
    linarith
  · subst heq; exact hgb

/-- Such a map also sends the largest element to the largest element and restricts to the sets
without their maxima. -/
private theorem g_top (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) (g : ℝ → ℝ)
    (hg : StrictMonoOn g ↑B) (hgB : g '' ↑B = ↑A) :
    g (B.max' hB) = A.max' hA ∧ g '' ↑(B.erase (B.max' hB)) = ↑(A.erase (A.max' hA)) := by
  have hmem : g (B.max' hB) ∈ A := by
    have := Set.mem_image_of_mem g (Finset.mem_coe.mpr (B.max'_mem hB))
    rw [hgB] at this; exact this
  have htop : g (B.max' hB) = A.max' hA := by
    apply le_antisymm (A.le_max' _ hmem)
    obtain ⟨b, hb, hgb⟩ : A.max' hA ∈ g '' ↑B := by rw [hgB]; exact A.max'_mem hA
    rw [← hgb]
    exact hg.monotoneOn hb (B.max'_mem hB) (B.le_max' b hb)
  refine ⟨htop, ?_⟩
  ext t
  simp only [Set.mem_image, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, ⟨hb, hbm⟩, rfl⟩
    refine ⟨?_, fun h => hbm (hg.injOn hb (B.max'_mem hB) (h.trans htop.symm))⟩
    have := Set.mem_image_of_mem g (Finset.mem_coe.mpr hb)
    rw [hgB] at this; exact this
  · rintro ⟨ht, htm⟩
    obtain ⟨b, hb, rfl⟩ : t ∈ g '' ↑B := by rw [hgB]; exact ht
    exact ⟨b, ⟨hb, fun h => htm (h ▸ htop)⟩, rfl⟩

/-- Two minimum-order spaces whose centers correspond under a map `g`, strictly increasing on the
center of `Y`, admit a bijection carrying `ρ` to `d` through `g`. -/
private theorem sim (n : ℕ) : ∀ (X Y : Type) [MetricSpace X] [IsUltrametricDist X] [Finite X]
    [MetricSpace Y] [IsUltrametricDist Y] [Finite Y] (A B : Finset ℝ), A.card = n + 1 →
    B.card = n + 1 → center X = ↑A → center Y = ↑B → Nat.card X = 2 ^ n →
    Nat.card Y = 2 ^ n → ∀ g : ℝ → ℝ, StrictMonoOn g ↑B → g '' ↑B = ↑A →
    ∃ Φ : X → Y, ∀ x y : X, dist x y = g (dist (Φ x) (Φ y)) := by
  induction n with
  | zero =>
    intro X Y _ _ _ _ _ _ A B _ _ hcX hcY hX hY g hg hgB
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.mp hX
    obtain ⟨y0⟩ := nonempty_of_card hY
    have h0 := g_zero ↑A ↑B (hcX ▸ zero_mem_center X) (hcY ▸ zero_mem_center Y)
      (fun a ha => (show a ∈ center X by rw [hcX]; exact ha).1)
      (fun b hb => (show b ∈ center Y by rw [hcY]; exact hb).1) g hg hgB
    refine ⟨fun _ => y0, fun x y => ?_⟩
    rw [Subsingleton.elim x y, dist_self, dist_self, h0]
  | succ n ih =>
    intro X Y _ _ _ _ _ _ A B hA hB hcX hcY hX hY g hg hgB
    have hcardA : A.card = n + 2 := hA
    have hcardB : B.card = n + 2 := hB
    have hneA : A.Nonempty := Finset.card_pos.mp (by omega)
    have hneB : B.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨htop, himg⟩ := g_top A B hneA hneB g hg hgB
    have hmX : A.max' hneA ∈ center X := by rw [hcX]; exact A.max'_mem hneA
    have hmY : B.max' hneB ∈ center Y := by rw [hcY]; exact B.max'_mem hneB
    obtain ⟨p⟩ := nonempty_of_card hX
    obtain ⟨p'⟩ := nonempty_of_card hY
    obtain ⟨q, hq⟩ := hmX.2 p
    obtain ⟨q', hq'⟩ := hmY.2 p'
    obtain ⟨hbX, hcovX, hdisX⟩ := split X n A hcX hcardA hX p q hq
    obtain ⟨hbY, hcovY, hdisY⟩ := split Y n B hcY hcardB hY p' q' hq'
    set m := A.max' hneA
    set m' := B.max' hneB
    have hEA : (A.erase m).card = n + 1 := by
      rw [Finset.card_erase_of_mem (A.max'_mem hneA)]; omega
    have hEB : (B.erase m').card = n + 1 := by
      rw [Finset.card_erase_of_mem (B.max'_mem hneB)]; omega
    have hg' : StrictMonoOn g ↑(B.erase m') :=
      hg.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
    obtain ⟨hpX, hpcX⟩ := hbX p (Or.inr hq)
    obtain ⟨hqX, hqcX⟩ := hbX q (Or.inl (by rw [dist_comm]; exact hq))
    obtain ⟨hpY, hpcY⟩ := hbY p' (Or.inr hq')
    obtain ⟨hqY, hqcY⟩ := hbY q' (Or.inl (by rw [dist_comm]; exact hq'))
    obtain ⟨Φ1, hΦ1⟩ := ih _ _ (A.erase m) (B.erase m') hEA hEB hpcX hpcY hpX hpY g hg' himg
    obtain ⟨Φ2, hΦ2⟩ := ih _ _ (A.erase m) (B.erase m') hEA hEB hqcX hqcY hqX hqY g hg' himg
    classical
    let Φ : X → Y := fun x =>
      if h : dist p x < m then (Φ1 ⟨x, h⟩).1 else (Φ2 ⟨x, (hcovX x).resolve_left h⟩).1
    have hf1 : ∀ x (h : dist p x < m), Φ x = (Φ1 ⟨x, h⟩).1 := fun x h => by
      simp only [Φ, h, ↓reduceDIte]
    have hf2 : ∀ x (h : ¬ dist p x < m), Φ x = (Φ2 ⟨x, (hcovX x).resolve_left h⟩).1 :=
      fun x h => by simp only [Φ, h, ↓reduceDIte]
    have hin1 : ∀ x (h : dist p x < m), dist p' (Φ x) < m' := fun x h => by
      rw [hf1 x h]; exact (Φ1 ⟨x, h⟩).2
    have hout2 : ∀ x (h : ¬ dist p x < m), ¬ dist p' (Φ x) < m' := fun x h hlt => by
      rw [hf2 x h] at hlt
      exact hdisY _ ⟨hlt, (Φ2 ⟨x, (hcovX x).resolve_left h⟩).2⟩
    have hmXle := le_max_center X A hcX hneA
    have hmYle := le_max_center Y B hcY hneB
    refine ⟨Φ, fun x y => ?_⟩
    by_cases hx : dist p x < m <;> by_cases hy : dist p y < m
    · rw [hf1 x hx, hf1 y hy]
      exact hΦ1 ⟨x, hx⟩ ⟨y, hy⟩
    · rw [cross p x y hmXle hx hy, cross p' (Φ x) (Φ y) hmYle (hin1 x hx) (hout2 y hy), htop]
    · rw [dist_comm, dist_comm (Φ x), cross p y x hmXle hy hx,
        cross p' (Φ y) (Φ x) hmYle (hin1 y hy) (hout2 x hx), htop]
    · rw [hf2 x hx, hf2 y hy]
      exact hΦ2 ⟨x, _⟩ ⟨y, _⟩

/-- On a nonempty target, a weak similarity carries the center bijectively onto the center. -/
private theorem center_ncard_aux {X Y : Type} [MetricSpace X] [MetricSpace Y] (Φ : X ≃ Y)
    (f : ℝ → ℝ) (hf : StrictMonoOn f (distances Y)) (hd : ∀ x y : X, dist x y = f (dist (Φ x) (Φ y)))
    (q0 : Y) : (center X).encard = (center Y).encard := by
  have hCD : center Y ⊆ distances Y := fun t ht => by
    obtain ⟨y, hy⟩ := ht.2 q0
    exact ⟨y, q0, hy⟩
  have heq : center X = f '' center Y := by
    ext s
    constructor
    · rintro ⟨hs0, hs⟩
      obtain ⟨x, hx⟩ := hs (Φ.symm q0)
      have e2 : f (dist (Φ x) q0) = s := by rw [← hx, hd, Φ.apply_symm_apply]
      refine ⟨dist (Φ x) q0, ⟨dist_nonneg, fun q => ?_⟩, e2⟩
      obtain ⟨x', hx'⟩ := hs (Φ.symm q)
      have e1 : f (dist (Φ x') q) = s := by rw [← hx', hd, Φ.apply_symm_apply]
      exact ⟨Φ x', hf.injOn ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ (e1.trans e2.symm)⟩
    · rintro ⟨t, ⟨ht0, ht⟩, rfl⟩
      refine ⟨?_, fun p => ?_⟩
      · obtain ⟨y, hy⟩ := ht q0
        have : dist (Φ.symm y) (Φ.symm q0) = f t := by
          rw [hd, Φ.apply_symm_apply, Φ.apply_symm_apply, hy]
        rw [← this]
        exact dist_nonneg
      · obtain ⟨y, hy⟩ := ht (Φ p)
        refine ⟨Φ.symm y, ?_⟩
        rw [hd, Φ.apply_symm_apply, hy]
  rw [heq]
  exact (hf.injOn.mono hCD).encard_image

/-- A weak similarity preserves the number of central distances, finite or infinite. -/
private theorem center_ncard {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (h : WeaklySimilar X Y) : (center X).encard = (center Y).encard := by
  obtain ⟨Φ, f, hf, hd⟩ := h
  rcases isEmpty_or_nonempty Y with hY | hY
  · have hX : IsEmpty X := Φ.isEmpty
    have e1 : center X = {t | 0 ≤ t} := by ext t; simp [center]
    have e2 : center Y = {t | 0 ≤ t} := by ext t; simp [center]
    rw [e1, e2]
  · obtain ⟨q0⟩ := hY
    exact center_ncard_aux Φ f hf hd q0

/-- A nonempty finite space has finite center. -/
private theorem center_finite (X : Type) [MetricSpace X] [Finite X] (p : X) :
    (center X).Finite :=
  (Set.finite_range (fun y : X => dist y p)).subset fun t ht => by
    obtain ⟨y, hy⟩ := ht.2 p
    exact ⟨y, hy⟩

/-- Two minimum-order spaces with equally many points are weakly similar. -/
private theorem weak_of_mcd {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
    [MetricSpace Y] [IsUltrametricDist Y] [Finite Y]
    (hX : Nat.card X = 2 ^ ((center X).ncard - 1)) (hY : Nat.card Y = 2 ^ ((center Y).ncard - 1))
    (hXY : Nat.card X = Nat.card Y) : WeaklySimilar X Y := by
  classical
  obtain ⟨p⟩ := nonempty_of_card hX
  obtain ⟨p'⟩ := nonempty_of_card hY
  have hfinX := center_finite X p
  have hfinY := center_finite Y p'
  set A := hfinX.toFinset with hAdef
  set B := hfinY.toFinset with hBdef
  have hA : center X = ↑A := by simp [A]
  have hB : center Y = ↑B := by simp [B]
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨0, by simp [A, zero_mem_center X]⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, by simp [B, zero_mem_center Y]⟩
  have hncX : (center X).ncard = A.card := by rw [hA, Set.ncard_coe_finset]
  have hncY : (center Y).ncard = B.card := by rw [hB, Set.ncard_coe_finset]
  have hAB : A.card = B.card := by
    have h := hXY
    rw [hX, hY, hncX, hncY] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  set n := A.card - 1
  have hAc : A.card = n + 1 := by omega
  have hBc : B.card = n + 1 := by omega
  let e : { x // x ∈ B } ≃o { x // x ∈ A } :=
    (B.orderIsoOfFin hBc).symm.trans (A.orderIsoOfFin hAc)
  let g : ℝ → ℝ := fun t => if ht : t ∈ B then (e ⟨t, ht⟩ : ℝ) else 0
  have hgB : ∀ t (ht : t ∈ B), g t = (e ⟨t, ht⟩ : ℝ) := fun t ht => by
    simp only [g, ht, ↓reduceDIte]
  have hg : StrictMonoOn g ↑B := by
    intro a ha b hb hab
    rw [hgB a ha, hgB b hb]
    exact e.strictMono (Subtype.mk_lt_mk.mpr hab)
  have himg : g '' ↑B = ↑A := by
    ext t
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [hgB b hb]
      exact (e ⟨b, hb⟩).2
    · intro ht
      refine ⟨e.symm ⟨t, ht⟩, (e.symm ⟨t, ht⟩).2, ?_⟩
      rw [hgB _ (e.symm ⟨t, ht⟩).2]
      simp
  have hXn : Nat.card X = 2 ^ n := by rw [hX, hncX]
  have hYn : Nat.card Y = 2 ^ n := by rw [hY, hncY, ← hAB]
  obtain ⟨Φ, hΦ⟩ := sim n X Y A B hAc hBc hA hB hXn hYn g hg himg
  have h0 : g 0 = 0 := g_zero ↑A ↑B (hA ▸ zero_mem_center X) (hB ▸ zero_mem_center Y)
    (fun a ha => (show a ∈ center X by rw [hA]; exact ha).1)
    (fun b hb => (show b ∈ center Y by rw [hB]; exact hb).1) g hg himg
  have hinj : Function.Injective Φ := fun x y hxy => by
    have := hΦ x y
    rw [hxy, dist_self, h0] at this
    exact dist_eq_zero.mp this
  have hbij := hinj.bijective_of_nat_card_le (by rw [hXY])
  refine ⟨Equiv.ofBijective Φ hbij, g, hg.mono fun r hr => ?_, fun x y => hΦ x y⟩
  obtain ⟨a, b, rfl⟩ := hr
  rw [← hB]
  exact dist_mem_center n Y B hBc hB hYn a b

/-- Weak similarity of minimum-order ultrametric spaces (Dovgoshey–Rovenska, Conjecture 4.2):
two finite ultrametric spaces of minimum order `2^(|C| - 1)` with equally many points are weakly
similar; weak similarity of metric spaces preserves the number of central distances, finite or
infinite; hence if
`|X| = |Y| = 2^h` and `|C(X)| = h + 1`, then `|C(Y)| = h + 1` exactly when `X` and `Y` are weakly
similar. -/
theorem result :
    (∀ {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
      [MetricSpace Y] [IsUltrametricDist Y] [Finite Y],
      Nat.card X = 2 ^ ((center X).ncard - 1) → Nat.card Y = 2 ^ ((center Y).ncard - 1) →
      Nat.card X = Nat.card Y → WeaklySimilar X Y) ∧
    (∀ {X Y : Type} [MetricSpace X] [MetricSpace Y],
      WeaklySimilar X Y → (center X).encard = (center Y).encard) ∧
    (∀ {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
      [MetricSpace Y] [IsUltrametricDist Y] [Finite Y] (h : ℕ),
      Nat.card X = 2 ^ h → Nat.card Y = 2 ^ h → (center X).ncard = h + 1 →
      ((center Y).ncard = h + 1 ↔ WeaklySimilar X Y)) := by
  refine ⟨fun hX hY hXY => weak_of_mcd hX hY hXY, fun h => center_ncard h, ?_⟩
  intro X Y _ _ _ _ _ _ h hX hY hC
  constructor
  · intro hCY
    exact weak_of_mcd (by rw [hX, hC, Nat.add_sub_cancel]) (by rw [hY, hCY, Nat.add_sub_cancel])
      (by rw [hX, hY])
  · intro hW
    rw [Set.ncard_def, ← center_ncard hW, ← Set.ncard_def, hC]


end D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity
