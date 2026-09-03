/- GID: D5/S3/Analytic/AllOrder/WeightedMonomial
   generality: G
   mirror-B: D5/B/S3/Analytic/AllOrder/WeightedMonomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admissible weights canonically enumerate finite nonzero monomial sublevels. -/

/- Library-search audit trail (2026-09-03):
   * Repository searches for `GoldenMonomial`, `AdmissibleWeight`,
     `finite_sublevel`, and `weightedEulerLedger` found no existing declaration.
   * The golden-germ modules named in the task were inspected on `origin/dev`.
     They are instance-specific (`generality: I`) and expose no finite weighted
     monomial order, so importing them here would violate the generality
     boundary. This module consequently imports only Mathlib.
   * Pinned Mathlib supplies `Set.Finite.toFinset`, `Finset.sort`,
     `Finset.pairwise_sort`, `Finset.sort_nodup`, `Finset.mem_sort`,
     `List.SortedLT.eq_of_mem_iff`, and `ExistsAddOfLE.exists_add_of_le`.
     Their exact signatures were checked in the pinned environment.
   * The later Euler modules will use `MvPowerSeries.monomial`,
     `MvPowerSeries.monomial_mul_monomial`, `MvPowerSeries.coeff_mul`,
     `MvPowerSeries.invOfUnit`, `MvPowerSeries.mul_invOfUnit`,
     `MvPowerSeries.isUnit_iff_constantCoeff`, and `MvPowerSeries.trunc`.
     Those names were checked but are intentionally not used here: this first
     module stops at the finite ordered monomial ledger domain.

   STOPPING JUSTIFICATION: this node constructs the canonical finite list of
   all nonzero monomials below a weight threshold and proves its strict order
   and prefix compatibility. It does not define Euler factors, perform a
   coefficient cancellation, construct the weighted Euler ledger, or assert
   its uniqueness or nestedness. Those are the distinct later modules in the
   all-order extraction sequence. -/

import Mathlib

namespace D5.S3.Analytic.AllOrder.WeightedMonomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Bivariate monomial exponents for the all-order Euler ledger. -/
abbrev GoldenMonomial := Fin 2 →₀ ℕ

/-- An additive weight is admissible when every nonzero monomial has positive
weight, distinct monomials have distinct weights, and every strict sublevel is
finite. The three fields respectively support triangularity, a canonical
ordering, and finite elimination. -/
structure AdmissibleWeight (w : GoldenMonomial →+ ℝ) : Prop where
  positive : ∀ m, m ≠ 0 → 0 < w m
  injective : Function.Injective w
  finite_sublevel : ∀ T : ℝ, {m : GoldenMonomial | w m < T}.Finite

variable {w : GoldenMonomial →+ ℝ}

namespace AdmissibleWeight

variable (hw : AdmissibleWeight w)

/-- An additive weight sends the zero monomial to zero. -/
@[simp]
theorem weight_zero : w (0 : GoldenMonomial) = 0 :=
  w.map_zero

include hw

/-- The positivity field, exposed as a theorem for downstream rewriting. -/
theorem weight_pos {m : GoldenMonomial} (hm : m ≠ 0) : 0 < w m :=
  AdmissibleWeight.positive hw m hm

/-- Every monomial has nonnegative weight. -/
theorem weight_nonneg (m : GoldenMonomial) : 0 ≤ w m := by
  by_cases hm : m = 0
  · subst m
    simp
  · exact (weight_pos hw hm).le

/-- Zero is the unique monomial of weight zero. -/
@[simp]
theorem weight_eq_zero_iff {m : GoldenMonomial} : w m = 0 ↔ m = 0 := by
  constructor
  · intro hm
    exact AdmissibleWeight.injective hw (by simpa only [map_zero] using hm)
  · rintro rfl
    simp

/-- A monomial has nonzero weight exactly when it is nonzero. -/
@[simp]
theorem weight_ne_zero_iff {m : GoldenMonomial} : w m ≠ 0 ↔ m ≠ 0 := by
  exact not_congr (weight_eq_zero_iff hw)

/-- Positivity can be read as a characterization of nonzero monomials. -/
@[simp]
theorem weight_pos_iff {m : GoldenMonomial} : 0 < w m ↔ m ≠ 0 := by
  constructor
  · intro hm hzero
    subst m
    exact (lt_irrefl (0 : ℝ)) (by simpa only [map_zero] using hm)
  · exact weight_pos hw

omit hw in
/-- Weight is additive on monomial exponents. -/
theorem weight_add (m n : GoldenMonomial) : w (m + n) = w m + w n :=
  w.map_add m n

/-- Adding a nonzero monomial strictly raises weight. -/
theorem weight_lt_add_right (m : GoldenMonomial) {n : GoldenMonomial}
    (hn : n ≠ 0) : w m < w (m + n) := by
  rw [weight_add]
  linarith [weight_pos hw hn]

/-- The right summand is nonzero exactly when addition strictly raises the
weight of the left summand. -/
theorem weight_lt_add_right_iff (m n : GoldenMonomial) :
    w m < w (m + n) ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst n
    exact (lt_irrefl (w m)) (by simpa only [map_zero, add_zero] using h)
  · exact weight_lt_add_right hw m

/-- Adding a nonzero monomial on the left strictly raises weight. -/
theorem weight_lt_add_left {m : GoldenMonomial} (hm : m ≠ 0)
    (n : GoldenMonomial) : w n < w (m + n) := by
  rw [add_comm]
  exact weight_lt_add_right hw n hm

omit hw in
/-- Adding the same monomial on the left preserves and reflects weight comparison. -/
theorem weight_add_left_lt_iff (k m n : GoldenMonomial) :
    w (k + m) < w (k + n) ↔ w m < w n := by
  simp only [weight_add]
  exact add_lt_add_iff_left (w k)

omit hw in
/-- Adding the same monomial on the right preserves and reflects weight comparison. -/
theorem weight_add_right_lt_iff (k m n : GoldenMonomial) :
    w (m + k) < w (n + k) ↔ w m < w n := by
  simp only [weight_add]
  exact add_lt_add_iff_right (w k)

/-- The additive weight is monotone for the coordinatewise order on
monomials. -/
theorem weight_mono : Monotone w := by
  intro m n hmn
  obtain ⟨d, rfl⟩ := exists_add_of_le hmn
  rw [weight_add]
  exact le_add_of_nonneg_right (weight_nonneg hw d)

/-- The additive weight is strictly monotone for the coordinatewise order. -/
theorem weight_strictMono : StrictMono w := by
  intro m n hmn
  obtain ⟨d, rfl⟩ := exists_add_of_le hmn.le
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact hmn.ne (by simp)
  exact weight_lt_add_right hw m hd

/-- Coordinatewise comparison can therefore be discharged at the weight
level. -/
theorem weight_le_of_le {m n : GoldenMonomial} (hmn : m ≤ n) :
    w m ≤ w n :=
  weight_mono hw hmn

/-- A strict coordinatewise comparison gives a strict comparison of weights. -/
theorem weight_lt_of_lt {m n : GoldenMonomial} (hmn : m < n) :
    w m < w n :=
  weight_strictMono hw hmn

/-- Each nonzero coordinate basis monomial has positive weight. -/
theorem weight_single_pos (i : Fin 2) {a : ℕ} (ha : a ≠ 0) :
    0 < w (Finsupp.single i a) := by
  exact weight_pos hw (Finsupp.single_ne_zero.mpr ha)

omit hw in
/-- The strict weight sublevel as a set. -/
def weightSublevelSet (w : GoldenMonomial →+ ℝ) (T : ℝ) :
    Set GoldenMonomial :=
  {m | w m < T}

/-- Admissibility makes each strict weight sublevel finite. -/
theorem weightSublevelSet_finite (T : ℝ) :
    (weightSublevelSet w T).Finite := by
  simpa [weightSublevelSet] using AdmissibleWeight.finite_sublevel hw T

/-- Closed sublevels are finite as well. -/
theorem closedWeightSublevelSet_finite (T : ℝ) :
    {m : GoldenMonomial | w m ≤ T}.Finite := by
  apply (AdmissibleWeight.finite_sublevel hw (T + 1)).subset
  intro m hm
  change w m ≤ T at hm
  change w m < T + 1
  linarith

/-- Every exact weight fiber is finite. -/
theorem weightFiber_finite (T : ℝ) :
    {m : GoldenMonomial | w m = T}.Finite := by
  exact (closedWeightSublevelSet_finite hw T).subset (by
    intro m hm
    change w m = T at hm
    change w m ≤ T
    exact hm.le)

/-- The computable-facing finite carrier of a strict sublevel. Its value is
noncomputable only because no decidable comparison procedure for real weights
is selected. -/
noncomputable def weightSublevel (w : GoldenMonomial →+ ℝ)
    (hw : AdmissibleWeight w) (T : ℝ) : Finset GoldenMonomial :=
  (weightSublevelSet_finite hw T).toFinset

/-- Membership in the finite carrier is exactly the strict weight bound. -/
@[simp]
theorem mem_weightSublevel {T : ℝ} {m : GoldenMonomial} :
    m ∈ weightSublevel w hw T ↔ w m < T := by
  simp [weightSublevel, weightSublevelSet]

/-- The zero monomial belongs precisely at a positive threshold. -/
@[simp]
theorem zero_mem_weightSublevel {T : ℝ} :
    (0 : GoldenMonomial) ∈ weightSublevel w hw T ↔ 0 < T := by
  simp

/-- A strict sublevel is empty exactly when its threshold is nonpositive. -/
theorem weightSublevel_eq_empty_iff {T : ℝ} :
    weightSublevel w hw T = ∅ ↔ T ≤ 0 := by
  constructor
  · intro hempty
    by_contra hT
    have hzero : (0 : GoldenMonomial) ∈ weightSublevel w hw T := by
      simp [lt_of_not_ge hT]
    simp [hempty] at hzero
  · intro hT
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    rw [mem_weightSublevel] at hm
    exact (not_lt_of_ge (hT.trans (weight_nonneg hw m))) hm

/-- Strict sublevel carriers are monotone in the threshold. -/
theorem weightSublevel_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    weightSublevel w hw T₁ ⊆ weightSublevel w hw T₂ := by
  intro m hm
  rw [mem_weightSublevel] at hm ⊢
  exact lt_of_lt_of_le hm hT

/-- Remove the zero monomial before an Euler elimination fold. -/
noncomputable def positiveWeightSublevel (w : GoldenMonomial →+ ℝ)
    (hw : AdmissibleWeight w) (T : ℝ) :
    Finset GoldenMonomial :=
  (weightSublevel w hw T).erase 0

/-- The positive finite carrier contains exactly the nonzero monomials below
the threshold. -/
@[simp]
theorem mem_positiveWeightSublevel {T : ℝ} {m : GoldenMonomial} :
    m ∈ positiveWeightSublevel w hw T ↔ m ≠ 0 ∧ w m < T := by
  simp [positiveWeightSublevel]

/-- Zero never occurs in the positive finite carrier. -/
@[simp]
theorem zero_not_mem_positiveWeightSublevel (T : ℝ) :
    (0 : GoldenMonomial) ∉ positiveWeightSublevel w hw T := by
  simp

/-- Positive finite carriers are monotone in the threshold. -/
theorem positiveWeightSublevel_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    positiveWeightSublevel w hw T₁ ⊆
      positiveWeightSublevel w hw T₂ := by
  intro m hm
  rw [mem_positiveWeightSublevel] at hm ⊢
  exact ⟨hm.1, lt_of_lt_of_le hm.2 hT⟩

/-- A nonpositive threshold has no positive monomials below it. -/
theorem positiveWeightSublevel_eq_empty_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    positiveWeightSublevel w hw T = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [mem_positiveWeightSublevel] at hm
  exact (not_lt_of_ge (hT.trans (weight_nonneg hw m))) hm.2

/-- A finitely supported integer ledger whose support is below the threshold
is supported on the finite sublevel carrier. -/
theorem support_subset_weightSublevel
    (L : GoldenMonomial →₀ ℤ) (T : ℝ)
    (hL : ∀ m ∈ L.support, w m < T) :
    L.support ⊆ weightSublevel w hw T := by
  intro m hm
  rw [mem_weightSublevel]
  exact hL m hm

/-- If the constant ledger entry vanishes, the same support lies in the
positive sublevel carrier. -/
theorem support_subset_positiveWeightSublevel
    (L : GoldenMonomial →₀ ℤ) (T : ℝ) (hzero : L 0 = 0)
    (hL : ∀ m ∈ L.support, w m < T) :
    L.support ⊆ positiveWeightSublevel w hw T := by
  intro m hm
  rw [mem_positiveWeightSublevel]
  constructor
  · intro hmzero
    subst m
    exact (Finsupp.mem_support_iff.mp hm) hzero
  · exact hL m hm

/-- The canonical elimination order: all nonzero sublevel monomials sorted by
the order pulled back from their injective real weights. -/
noncomputable def increasingWeightSublevel (w : GoldenMonomial →+ ℝ)
    (hw : AdmissibleWeight w) (T : ℝ) :
    List GoldenMonomial :=
  let r := fun m n : GoldenMonomial => w m ≤ w n
  let _ : DecidableRel r := Classical.decRel r
  let _ : IsTrans GoldenMonomial r :=
    ⟨fun _ _ _ hmn hnk => hmn.trans hnk⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ hmn hnm => hw.injective (le_antisymm hmn hnm)⟩
  let _ : Std.Total r :=
    ⟨fun m n => le_total (w m) (w n)⟩
  (positiveWeightSublevel w hw T).sort r

/-- Membership in the canonical list is exactly nonzero sublevel membership. -/
@[simp]
theorem mem_increasingWeightSublevel {T : ℝ} {m : GoldenMonomial} :
    m ∈ increasingWeightSublevel w hw T ↔ m ≠ 0 ∧ w m < T := by
  simp [increasingWeightSublevel]

/-- The canonical list contains no repeated monomial. -/
theorem increasingWeightSublevel_nodup (T : ℝ) :
    (increasingWeightSublevel w hw T).Nodup := by
  simp [increasingWeightSublevel]

/-- Weights strictly increase along the canonical list. -/
theorem increasingWeightSublevel_pairwise (T : ℝ) :
    (increasingWeightSublevel w hw T).Pairwise
      (fun m n => w m < w n) := by
  let r := fun m n : GoldenMonomial => w m ≤ w n
  let _ : DecidableRel r := Classical.decRel r
  let _ : IsTrans GoldenMonomial r :=
    ⟨fun _ _ _ hmn hnk => hmn.trans hnk⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ hmn hnm => hw.injective (le_antisymm hmn hnm)⟩
  let _ : Std.Total r :=
    ⟨fun m n => le_total (w m) (w n)⟩
  have hle :
      ((positiveWeightSublevel w hw T).sort r).Pairwise r :=
    Finset.pairwise_sort _ r
  have hne :
      ((positiveWeightSublevel w hw T).sort r).Pairwise
        (fun m n => m ≠ n) :=
    Finset.sort_nodup _ r
  rw [increasingWeightSublevel]
  exact List.Pairwise.imp₂ (fun _ _ hle hne =>
    lt_of_le_of_ne hle (fun hweight => hne (hw.injective hweight))) hle hne

/-- The canonical list has the cardinality of the positive finite carrier. -/
theorem length_increasingWeightSublevel (T : ℝ) :
    (increasingWeightSublevel w hw T).length =
      (positiveWeightSublevel w hw T).card := by
  simp [increasingWeightSublevel]

/-- Every canonical-list entry has positive weight. -/
theorem weight_pos_of_mem_increasingWeightSublevel
    {T : ℝ} {m : GoldenMonomial}
    (hm : m ∈ increasingWeightSublevel w hw T) : 0 < w m :=
  weight_pos hw
    ((mem_increasingWeightSublevel (w := w) (hw := hw)).mp hm).1

omit hw in
private theorem filter_eq_takeWhile_of_pairwise_lt
    {l : List GoldenMonomial} {T : ℝ}
    (hl : l.Pairwise (fun m n => w m < w n)) :
    l.filter (fun m => decide (w m < T)) =
      l.takeWhile (fun m => decide (w m < T)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      by_cases ha : w a < T
      · simpa [ha] using ih hl.2
      · have hnone : ∀ b ∈ l, T ≤ w b := by
          intro b hb
          have hab : w a < w b := hl.1 b hb
          exact le_of_not_gt (fun hbt => ha (lt_trans hab hbt))
        have hfilter : l.filter (fun m => decide (w m < T)) = [] :=
          List.filter_eq_nil_iff.mpr (fun b hb => by
            simpa only [decide_eq_true_eq] using not_lt_of_ge (hnone b hb))
        simp [ha, hfilter]

/-- Filtering a larger canonical sublevel list at a smaller threshold recovers
the smaller canonical list. -/
theorem filter_increasingWeightSublevel {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (increasingWeightSublevel w hw T₂).filter
        (fun m => decide (w m < T₁)) =
      increasingWeightSublevel w hw T₁ := by
  let r := fun m n : GoldenMonomial => w m < w n
  let _ : Std.Antisymm r :=
    ⟨fun _ _ hmn hnm => (lt_asymm hmn hnm).elim⟩
  let _ : Std.Irrefl r :=
    ⟨fun m => lt_irrefl (w m)⟩
  apply List.Pairwise.eq_of_mem_iff (r := r)
  · exact (increasingWeightSublevel_pairwise hw T₂).filter _
  · exact increasingWeightSublevel_pairwise hw T₁
  · intro m
    simp only [List.mem_filter, mem_increasingWeightSublevel,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hm, -⟩, hmT₁⟩
      exact ⟨hm, hmT₁⟩
    · rintro ⟨hm, hmT₁⟩
      exact ⟨⟨hm, lt_of_lt_of_le hmT₁ hT⟩, hmT₁⟩

/-- The smaller canonical sublevel is the threshold prefix of every larger
canonical sublevel. -/
theorem takeWhile_increasingWeightSublevel {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (increasingWeightSublevel w hw T₂).takeWhile
        (fun m => decide (w m < T₁)) =
      increasingWeightSublevel w hw T₁ := by
  rw [← filter_eq_takeWhile_of_pairwise_lt
    (increasingWeightSublevel_pairwise hw T₂)]
  exact filter_increasingWeightSublevel hw hT

/-- Threshold enlargement preserves the old elimination order as an initial
segment. This is the structural input for later ledger nestedness. -/
theorem increasingWeightSublevel_prefix {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (increasingWeightSublevel w hw T₁).IsPrefix
      (increasingWeightSublevel w hw T₂) := by
  rw [← takeWhile_increasingWeightSublevel hw hT]
  exact List.takeWhile_prefix _

/-- The canonical finite weighted-monomial interface used by the later Euler
fold: exact membership, strict weight order, and compatibility of all larger
thresholds with the current initial segment. -/
theorem admissible_weight_ordered_sublevel_spec (T : ℝ) :
    let l := increasingWeightSublevel w hw T
    l.Nodup ∧
      (∀ m : GoldenMonomial, m ∈ l ↔ m ≠ 0 ∧ w m < T) ∧
      (∀ m : GoldenMonomial, m ∈ l → 0 < w m) ∧
      l.Pairwise (fun m n => w m < w n) ∧
      (∀ T' : ℝ, T ≤ T' →
        l.IsPrefix (increasingWeightSublevel w hw T')) := by
  dsimp only
  exact ⟨increasingWeightSublevel_nodup hw T,
    fun m => mem_increasingWeightSublevel (w := w) (hw := hw),
    fun _ hm => weight_pos_of_mem_increasingWeightSublevel hw hm,
    increasingWeightSublevel_pairwise hw T,
    fun T' hT => increasingWeightSublevel_prefix hw hT⟩

#print axioms admissible_weight_ordered_sublevel_spec
end AdmissibleWeight
end
end D5.S3.Analytic.AllOrder.WeightedMonomial
