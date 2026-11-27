/- GID: D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim; result=D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1; claim=D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim
   digest: A normalized two-letter rational array satisfies the printed truncated shuffle equations but violates a necessary membrane signature identity. -/

import D5.S3.Quantum.Transport.MatrixUnitDyson

section

-- BiaffineCell

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

open Filter Set
open scoped Topology

-- One open cell of a source patch. The derivatives refer to the actual function.
private theorem mixed_on_open_cell (X : ℝ → ℝ → ℝ) (a b c d l r u v x y : ℝ)
    (hx : x ∈ Ioo l r) (hy : y ∈ Ioo u v)
    (hpatch : ∀ s ∈ Ioo l r, ∀ t ∈ Ioo u v, X s t = a + b*s + c*t + d*s*t) :
    deriv (fun s => deriv (X s) y) x = d := by
  have outerModel : HasDerivAt (fun s : ℝ => c + d*s) d x := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id x).const_mul d).const_add c)
  apply (outerModel.congr_of_eventuallyEq ?_).deriv
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with s hs
  have innerModel : HasDerivAt (fun t : ℝ => a + b*s + c*t + d*s*t) (c + d*s) y := by
    have h₁ : HasDerivAt (fun t : ℝ => c*t) c y := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul c
    have h₂ : HasDerivAt (fun t : ℝ => d*s*t) (d*s) y := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul (d*s)
    exact (h₁.const_add (a+b*s)).add h₂
  have heq : X s =ᶠ[𝓝 y] fun t => a + b*s + c*t + d*s*t := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht using hpatch s hs t ht
  exact (innerModel.congr_of_eventuallyEq heq).deriv

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

end

section

-- Chamber

open MeasureTheory Set Function
open scoped BigOperators
open D5.S3.Quantum.Transport.MatrixUnitDyson

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

abbrev Rank (l : ℕ) := Equiv.Perm (Fin l)

def insertionRank (p : Fin 4) : Rank 4 :=
  (finSuccEquiv' (0 : Fin 4)).trans (finSuccEquiv' p).symm

private theorem rank_zero (p : Fin 4) : insertionRank p 0 = p := by
  apply (finSuccEquiv' p).injective
  simp [insertionRank]

private theorem rank_tail (p : Fin 4) (i : Fin 3) :
    insertionRank p ((0 : Fin 4).succAbove i) = p.succAbove i := by
  apply (finSuccEquiv' p).injective
  simp [insertionRank]

private theorem mem_reversed_orderedSimplex (y : Fin 3 → ℝ) :
    y ∘ Fin.revPerm ∈ orderedSimplex 3 1 ↔ (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) ∧ Monotone y := by
  change ((∀ i : Fin 3, 0 ≤ y i.rev ∧ y i.rev ≤ 1) ∧
    ∀ i j : Fin 3, i ≤ j → y j.rev ≤ y i.rev) ↔ _
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using hb i.rev
    · simpa using hm j.rev i.rev (Fin.rev_le_rev.mpr hij)
  · rintro ⟨hb, hm⟩
    exact ⟨fun i => hb i.rev, fun _ _ hij => hm (Fin.rev_le_rev.mpr hij)⟩

section
set_option quotPrecheck false
local notation "V" => (Fin 4 → ℝ)
local notation "SplitSpace" => (ℝ × (Fin 3 → ℝ))
local notation "split₄" => (fun i : Fin 4 => MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)
local notation "reindex₄" => (fun p : Fin 4 => MeasurableEquiv.piCongrLeft (fun _ => ℝ) (insertionRank p))
local notation "cube₄" => (Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (0 : ℝ) 1))
local notation "simplex₄" => (cube₄ ∩ {x : V | StrictMono x})
local notation "closed₄" => (cube₄ ∩ {x : V | Monotone x})
local notation "simplex₃" => ({x : Fin 3 → ℝ | x ∘ Fin.revPerm ∈ orderedSimplex 3 1})
local notation "block₄" => (split₄ (0 : Fin 4) ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ simplex₃))
local notation "chamber₄" => (fun p : Fin 4 => reindex₄ p ⁻¹' simplex₄)

-- Insertion separately on the two axes for arbitrary integrable test functions.
private theorem insertion (g : V × V → ℝ) (hg : IntegrableOn g (block₄ ×ˢ block₄) volume) :
    (∫ x in block₄ ×ˢ block₄, g x) =
      ∑ p : Fin 4 × Fin 4, ∫ y in closed₄ ×ˢ closed₄,
        g ((reindex₄ p.1).symm y.1, (reindex₄ p.2).symm y.2) := by
  have hblock (x : V) :
      x ∈ block₄ ↔ x ∈ cube₄ ∧ Monotone (x ∘ (0 : Fin 4).succAbove) := by
    change (x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ (x ∘ (0 : Fin 4).succAbove) ∘ Fin.revPerm ∈
      orderedSimplex 3 1) ↔ _
    rw [mem_reversed_orderedSimplex]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply, ← and_assoc]
    rw [← Fin.forall_iff_succAbove (P := fun i => x i ∈ Set.Icc (0 : ℝ) 1) (0 : Fin 4)]
  have reindex_apply (p : Fin 4) (x : V) (i : Fin 4) :
      reindex₄ p x i = x ((insertionRank p).symm i) := by
    simpa using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (insertionRank p) x ((insertionRank p).symm i)
  have hmeas : MeasurableSet simplex₄ := by
    apply MeasurableSet.inter (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc)
    simp only [StrictMono, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ : i < j =>
        measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  have hsub (p : Fin 4) : chamber₄ p ⊆ block₄ := by
    intro x hx
    change reindex₄ p x ∈ simplex₄ at hx
    rw [hblock]
    refine ⟨?_, ?_⟩
    · intro i _
      simpa only [reindex_apply, Equiv.symm_apply_apply] using hx.1 (insertionRank p i) (mem_univ _)
    · intro i j hij
      have hmono : Monotone (reindex₄ p x) := (show StrictMono (reindex₄ p x) from hx.2).monotone
      have ht := hmono ((Fin.strictMono_succAbove p).monotone hij)
      change x ((0 : Fin 4).succAbove i) ≤ x ((0 : Fin 4).succAbove j)
      rw [← (insertionRank p).symm_apply_apply ((0 : Fin 4).succAbove i),
        ← (insertionRank p).symm_apply_apply ((0 : Fin 4).succAbove j), rank_tail, rank_tail]
      simpa only [reindex_apply] using ht
  have hdisjoint : Pairwise (Disjoint on chamber₄) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hp hq
    change reindex₄ p x ∈ simplex₄ at hp
    change reindex₄ q x ∈ simplex₄ at hq
    have sort_eq (r : Fin 4) (hr : reindex₄ r x ∈ simplex₄) :
        (insertionRank r).symm = Tuple.sort x := by
      apply Tuple.eq_sort_iff.mpr
      have hstrict : StrictMono (x ∘ (insertionRank r).symm) := by
        intro i j hij
        simpa only [reindex_apply, Function.comp_apply] using (show StrictMono (reindex₄ r x) from hr.2) hij
      exact ⟨hstrict.monotone, fun i j hij h => ((hstrict hij).ne h).elim⟩
    have hr := congrArg (fun e : Equiv.Perm (Fin 4) => e.symm 0) ((sort_eq p hp).trans (sort_eq q hq).symm)
    exact hpq (by simpa [rank_zero] using hr)
  have rank_unique : ∀ σ : Equiv.Perm (Fin 4),
      (∀ i j : Fin 3, i < j → σ ((0 : Fin 4).succAbove i) < σ ((0 : Fin 4).succAbove j)) →
        σ = insertionRank (σ 0) := by decide
  have ht : ∀ᵐ x : V ∂volume, Injective x := by
    simp only [Injective, ae_all_iff]
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    let tie : Set SplitSpace := {z | z.2 k = z.1}
    have hzero : (volume : Measure SplitSpace) tie = 0 := by
      apply Measure.measure_prod_null_of_ae_null
      · exact measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_fst
      · apply Filter.Eventually.of_forall
        intro a
        change (volume : Measure (Fin 3 → ℝ)) ((fun y : Fin 3 → ℝ => y k) ⁻¹' {a}) = 0
        exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) (measure_singleton a)
    have hpre := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) i).preimage_null hzero
    have heq : {z : V | ¬ (z i = z (i.succAbove k) → i = i.succAbove k)} =
        split₄ i ⁻¹' tie := by
      ext z
      change (¬ (z i = z (i.succAbove k) → i = i.succAbove k)) ↔ z (i.succAbove k) = z i
      have hn : i ≠ i.succAbove k := (Fin.succAbove_ne i k).symm
      simp [hn, eq_comm]
    rw [ae_iff]
    change (volume : Measure V) {z : V | ¬ (z i = z (i.succAbove k) → i = i.succAbove k)} = 0
    rw [heq]
    exact hpre
  have hclosed : simplex₄ =ᵐ[(volume : Measure V)] closed₄ := by
    filter_upwards [ht] with x hx
    apply propext
    change (x ∈ cube₄ ∧ StrictMono x) ↔ (x ∈ cube₄ ∧ Monotone x)
    exact ⟨fun h => ⟨h.1, h.2.monotone⟩, fun h => ⟨h.1, h.2.strictMono_of_injective hx⟩⟩
  have hcover : block₄ =ᵐ[(volume : Measure V)] ⋃ p : Fin 4, chamber₄ p := by
    filter_upwards [ht] with x hx
    change (x ∈ block₄) = (x ∈ ⋃ p : Fin 4, chamber₄ p)
    rw [eq_iff_iff, Set.mem_iUnion]
    refine ⟨?_, fun ⟨p, hp⟩ => hsub p hp⟩
    intro xb
    obtain ⟨hc, hm⟩ := (hblock x).mp xb
    let σ := Tuple.sort x
    have hs : StrictMono (x ∘ σ) := (Tuple.monotone_sort x).strictMono_of_injective (hx.comp σ.injective)
    have hinv := rank_unique σ.symm fun i j hij => by
      apply hs.lt_iff_lt.mp
      simpa [Function.comp_apply] using
        (hm.strictMono_of_injective (hx.comp (Fin.strictMono_succAbove (0 : Fin 4)).injective) hij)
    refine ⟨σ.symm 0, ?_⟩
    change reindex₄ (σ.symm 0) x ∈ simplex₄
    have hr : reindex₄ (σ.symm 0) x = x ∘ σ := by
      ext i
      rw [reindex_apply, ← hinv]
      rfl
    rw [hr]
    exact ⟨fun i _ => hc (σ i) (mem_univ _), hs⟩
  let chambers : Fin 4 × Fin 4 → Set (V × V) :=
    fun p => chamber₄ p.1 ×ˢ chamber₄ p.2
  have hcovers : block₄ ×ˢ block₄ =ᵐ[(volume : Measure (V × V))] ⋃ p, chambers p := by
    change _ =ᵐ[(volume : Measure V).prod volume] _
    rw [show (⋃ p, chambers p) =
      (⋃ p : Fin 4, chamber₄ p) ×ˢ (⋃ p : Fin 4, chamber₄ p) from
      Set.iUnion_prod chamber₄ chamber₄]
    exact Measure.set_prod_ae_eq hcover hcover
  have hsubs (p : Fin 4 × Fin 4) : chambers p ⊆ block₄ ×ˢ block₄ :=
    Set.prod_mono (hsub p.1) (hsub p.2)
  have hpairs : Pairwise (Disjoint on chambers) := by
    intro p q hn
    apply Set.disjoint_prod.mpr
    by_cases h : p.1 = q.1
    · exact Or.inr (hdisjoint (fun heq => hn (Prod.ext h heq)))
    · exact Or.inl (hdisjoint h)
  have hmes (p : Fin 4 × Fin 4) : MeasurableSet (chambers p) :=
    ((reindex₄ p.1).measurable hmeas).prod ((reindex₄ p.2).measurable hmeas)
  rw [setIntegral_congr_set hcovers, integral_iUnion_fintype hmes hpairs (fun p => hg.mono_set (hsubs p))]
  apply Finset.sum_congr rfl
  intro p _
  let e := (reindex₄ p.1).prodCongr (reindex₄ p.2)
  have hm : MeasurePreserving e (volume : Measure (V × V)) volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) (insertionRank p.1)).prod
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) (insertionRank p.2))
  have hpre : e ⁻¹' (simplex₄ ×ˢ simplex₄) = chambers p := by
    ext x
    rfl
  have hchange := (hm.restrict_preimage (hmeas.prod hmeas)).integral_comp' (fun y => g (e.symm y))
  change (∫ x in chambers p, g x) = (∫ y in closed₄ ×ˢ closed₄, g (e.symm y))
  have hclosed_prod : simplex₄ ×ˢ simplex₄ =ᵐ[(volume : Measure (V × V))] closed₄ ×ˢ closed₄ :=
    Measure.set_prod_ae_eq hclosed hclosed
  rw [← setIntegral_congr_set hclosed_prod]
  simpa only [MeasurableEquiv.symm_apply_apply, hpre] using hchange
end

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

end

section

-- Grid

open Filter Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

abbrev Plane := ℝ × ℝ
abbrev UnitInterval : Set ℝ := Icc 0 1
abbrev UnitSquare : Set Plane := UnitInterval ×ˢ UnitInterval
abbrev Membrane (d : ℕ) := ℝ → ℝ → Fin d → ℝ

def gridPoint (m i : ℕ) : ℝ := (i : ℝ) / m

def openStrip (m : ℕ) (i : Fin m) : Set ℝ :=
  Ioo (gridPoint m i.val) (gridPoint m (i.val + 1))

def closedStrip (m : ℕ) (i : Fin m) : Set ℝ :=
  Icc (gridPoint m i.val) (gridPoint m (i.val + 1))

/-- Biaffine restrictions to all closed cells of a positive finite uniform grid.
The function represents an ambient extension of the square membrane. -/
def PiecewiseBilinear {d : ℕ} (X : Membrane d) : Prop :=
  ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧
    ∀ (i : Fin m) (j : Fin n) (c : Fin d), ∃ (a b e f : ℝ),
      ∀ s ∈ closedStrip m i, ∀ t ∈ closedStrip n j,
        X s t c = a + b * s + e * t + f * s * t

/-- The native mixed partial in the interior of a cell. Grid seams have measure zero. -/
def mixed {d : ℕ} (X : Membrane d) (c : Fin d) (z : Plane) : ℝ :=
  deriv (fun s => deriv (fun t => X s t c) z.2) z.1

private theorem openStrip_exists {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : x ∈ UnitInterval)
    (hseam : ∀ j : Fin (m + 1), x ≠ gridPoint m j.val) :
    ∃ i : Fin m, x ∈ openStrip m i := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : 0 ≤ x * m := mul_nonneg hx.1 hmR.le
  have h1 : x < 1 := lt_of_le_of_ne hx.2 (by
    simpa [gridPoint, hmR.ne'] using hseam ⟨m, Nat.lt_succ_self m⟩)
  let i := ⌊x * (m : ℝ)⌋₊
  have hi : i < m := (Nat.floor_lt h0).mpr (by simpa using mul_lt_mul_of_pos_right h1 hmR)
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · exact lt_of_le_of_ne ((div_le_iff₀ hmR).2 (Nat.floor_le h0))
      (Ne.symm (hseam ⟨i, hi.trans (Nat.lt_succ_self m)⟩))
  · apply (lt_div_iff₀ hmR).2
    simpa [i] using Nat.lt_floor_add_one (x * (m : ℝ))

private theorem openStrip_unique {m : ℕ} (hm : 0 < m) {i j : Fin m} {x : ℝ}
    (hi : x ∈ openStrip m i) (hj : x ∈ openStrip m j) : i = j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdisj {u v : Fin m} (huv : u < v) :
      Disjoint (openStrip m u) (openStrip m v) := by
    rw [Set.disjoint_left]
    intro y hu hv
    have h : u.val + 1 ≤ v.val := huv
    have hh : gridPoint m (u.val + 1) ≤ gridPoint m v.val := by
      unfold gridPoint
      exact div_le_div_of_nonneg_right (by exact_mod_cast h) hmR.le
    exact (hu.2.trans_le hh).not_gt hv.1
  rcases lt_trichotomy i j with h | h | h
  · exact (Set.disjoint_left.mp (hdisj h) hi hj).elim
  · exact h
  · exact (Set.disjoint_left.mp (hdisj h) hj hi).elim

private theorem ae_off_grid (m n : ℕ) : ∀ᵐ z : Plane ∂volume,
    (∀ i : Fin (m+1), z.1 ≠ gridPoint m i.val) ∧
      (∀ j : Fin (n+1), z.2 ≠ gridPoint n j.val) := by
  have h (p : ℕ) : ∀ᵐ x : ℝ ∂volume, ∀ i : Fin (p+1), x ≠ gridPoint p i.val := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    simp
  let μ : Measure ℝ := volume
  have hf : QuasiMeasurePreserving (Prod.fst : Plane → ℝ) (μ.prod μ) μ :=
    Measure.quasiMeasurePreserving_fst
  have hs : QuasiMeasurePreserving (Prod.snd : Plane → ℝ) (μ.prod μ) μ :=
    Measure.quasiMeasurePreserving_snd
  exact (hf.ae (h m)).and (hs.ae (h n))

def BoundedMeasurable {d : ℕ} (f : Fin d → Plane → ℝ) : Prop :=
  (∀ c, Measurable (f c)) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ c z, ‖f c z‖ ≤ M

private theorem mixed_representative {d : ℕ} {X : Membrane d} (hX : PiecewiseBilinear X) :
    ∃ f : Fin d → Plane → ℝ, BoundedMeasurable f ∧
      ∀ c, mixed X c =ᵐ[volume.restrict UnitSquare] f c := by
  classical
  obtain ⟨m, n, hm, hn, hpatch⟩ := hX
  choose a b e g h using hpatch
  let cell (ij : Fin m × Fin n) : Set Plane := openStrip m ij.1 ×ˢ openStrip n ij.2
  let f (c : Fin d) (z : Plane) :=
    ∑ ij : Fin m × Fin n, (cell ij).indicator (fun _ => g ij.1 ij.2 c) z
  have hcell (ij) : MeasurableSet (cell ij) := measurableSet_Ioo.prod measurableSet_Ioo
  have hf (c) : Measurable (f c) :=
    Finset.measurable_sum _ fun ij _ => measurable_const.indicator (hcell ij)
  let M (c : Fin d) := ∑ ij : Fin m × Fin n, ‖g ij.1 ij.2 c‖
  have hM (c) : 0 ≤ M c := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨f, ⟨hf, ∑ c, M c, Finset.sum_nonneg fun c _ => hM c, ?_⟩, ?_⟩
  · intro c z
    calc
      ‖f c z‖ ≤ ∑ ij : Fin m × Fin n,
          ‖(cell ij).indicator (fun _ => g ij.1 ij.2 c) z‖ :=
        norm_sum_le _ _
      _ ≤ M c := Finset.sum_le_sum fun ij _ => by
        by_cases hz : z ∈ cell ij
        · rw [indicator_of_mem hz]
        · rw [indicator_of_notMem hz, norm_zero]
          exact norm_nonneg _
      _ ≤ ∑ c, M c := Finset.single_le_sum (fun c _ => hM c) (Finset.mem_univ c)
  · intro c
    filter_upwards [ae_restrict_of_ae (ae_off_grid m n),
      ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz hsq
    obtain ⟨i, hi⟩ := openStrip_exists hm hsq.1 hz.1
    obtain ⟨j, hj⟩ := openStrip_exists hn hsq.2 hz.2
    have hder : mixed X c z = g i j c :=
      mixed_on_open_cell (fun s t => X s t c) _ _ _ _ _ _ _ _ _ _ hi hj
        (fun s hs t ht => h i j c s (Ioo_subset_Icc_self hs) t (Ioo_subset_Icc_self ht))
    rw [hder]
    symm
    unfold f
    rw [Finset.sum_eq_single (i, j)]
    · exact indicator_of_mem (show z ∈ cell (i,j) from ⟨hi, hj⟩) _
    · intro ij _ hne
      apply indicator_of_notMem
      intro hmem
      exact hne (Prod.ext (openStrip_unique hm hmem.1 hi) (openStrip_unique hn hmem.2 hj))
    · simp

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation
end

end

section

-- Shuffle

open scoped BigOperators

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

abbrev Word (d l : ℕ) := Fin l → Fin d
abbrev Array (R : Type) (d k : ℕ) := (l : Fin (k + 1)) → Word d l → Rank l → R

def blockRank {m n : ℕ} (α : Rank m) (β : Rank n) : Rank (m+n) :=
  finSumFinEquiv.permCongr (α.sumCongr β)

def shuffles (m n : ℕ) : Finset (Rank (m+n)) :=
  Finset.univ.filter fun π =>
    (∀ i j : Fin m, i < j → π (Fin.castAdd n i) < π (Fin.castAdd n j)) ∧
      (∀ i j : Fin n, i < j → π (Fin.natAdd m i) < π (Fin.natAdd m j))

def shuffleSum {R : Type} [AddCommMonoid R] {d m n : ℕ}
    (s : Word d (m+n) → Rank (m+n) → R)
    (u : Word d m) (v : Word d n) (b : Rank (m+n)) : R :=
  ∑ p ∈ (shuffles m n).product (shuffles m n),
    s (Fin.append u v ∘ p.1.symm) ((p.1.symm.trans b).trans p.2)

/-- The shuffle in Definition 2.6, including the inverse of the block permutation
and the empty basis element as unit. -/
def printedRhs {R : Type} [AddCommMonoid R] {d k : ℕ} (s : Array R d k)
    (m n : Fin (k+1)) (h : m.val + n.val ≤ k)
    (u : Word d m) (v : Word d n) (α : Rank m) (β : Rank n) : R :=
  if m.val = 0 then s n v β
  else if n.val = 0 then s m u α
  else shuffleSum (s ⟨m.val+n.val, Nat.lt_succ_of_le h⟩) u v (blockRank α β).symm

def Printed {R : Type} [Semiring R] {d k : ℕ} (s : Array R d k) : Prop :=
  ∀ (m n : Fin (k+1)) (h : m.val+n.val ≤ k)
    (u : Word d m) (v : Word d n) (α : Rank m) (β : Rank n),
    s m u α * s n v β = printedRhs s m n h u v α β

private theorem printed_cast {d k : ℕ} (s : Array ℚ d k) (hs : Printed s) :
    Printed (R := ℝ) (fun l w τ => (s l w τ : ℝ)) := by
  intro m n h u v α β
  have hr := congrArg (Rat.castHom ℝ) (hs m n h u v α β)
  unfold printedRhs at hr ⊢
  split_ifs at hr ⊢ <;> simpa [shuffleSum, map_sum] using hr

private theorem shuffles_one_three :
    shuffles 1 3 = Finset.univ.image insertionRank := by decide

def cycle231 : Rank 3 :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private theorem genuineSum_one_three {R : Type} [AddCommMonoid R] {d : ℕ}
    (s : Word d 4 → Rank 4 → R) (u : Word d 1) (v : Word d 3) (β : Rank 3) :
    shuffleSum s u v (blockRank (Equiv.refl _) β) =
      ∑ p : Fin 4 × Fin 4,
        s (Fin.append u v ∘ (insertionRank p.1).symm)
          (((insertionRank p.1).symm.trans (blockRank (Equiv.refl _) β)).trans
            (insertionRank p.2)) := by
  unfold shuffleSum
  rw [shuffles_one_three]
  have h := Finset.prodMap_image_product insertionRank insertionRank
    (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 4))
  rw [Finset.product_eq_sprod, ← h, Finset.univ_product_univ]
  apply Finset.sum_image
  intro p _ q _ hpq
  apply Prod.ext
  · simpa [rank_zero] using congrArg (fun t : Rank 4 × Rank 4 => t.1 0) hpq
  · simpa [rank_zero] using congrArg (fun t : Rank 4 × Rank 4 => t.2 0) hpq

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

end

section

-- Signature

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

abbrev Axis (l : ℕ) := Fin l → ℝ
abbrev Axes (l : ℕ) := Axis l × Axis l

def cube (l : ℕ) : Set (Axis l) := Set.pi Set.univ fun _ => UnitInterval

def simplex (l : ℕ) : Set (Axis l) := cube l ∩ {x | Monotone x}

private theorem measurableSet_simplex (l : ℕ) : MeasurableSet (simplex l) := by
  apply MeasurableSet.inter (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc)
  simp only [Monotone, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ : i ≤ j =>
      measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

private theorem cube_compact (l : ℕ) : IsCompact (cube l) :=
  isCompact_univ_pi fun _ => isCompact_Icc

def coordinate {l : ℕ} (i j : Fin l) (z : Axes l) : Plane := (z.1 i, z.2 j)

private theorem measurable_coordinate {l : ℕ} (i j : Fin l) : Measurable (coordinate i j) :=
  ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply j).comp measurable_snd)

private theorem quasiMeasurePreserving_coordinate {l : ℕ} (i j : Fin l) :
    QuasiMeasurePreserving (coordinate i j) volume volume := by
  have heval (k : Fin l) :
      QuasiMeasurePreserving (fun x : Axis l => x k) volume volume := by
    refine ⟨measurable_pi_apply k, Measure.AbsolutelyContinuous.mk fun t ht => ?_⟩
    rw [Measure.map_apply (measurable_pi_apply k) ht]
    exact fun h => Measure.pi_eval_preimage_null (fun _ : Fin l => (volume : Measure ℝ)) h
  exact (heval i).prodMap (heval j)

private theorem coordinate_maps {l : ℕ} (i j : Fin l) :
    MapsTo (coordinate i j) (cube l ×ˢ cube l) UnitSquare := by
  intro z hz
  exact ⟨hz.1 i (mem_univ _), hz.2 j (mem_univ _)⟩

def integrand {d l : ℕ} (f : Fin d → Plane → ℝ) (w : Word d l) (τ : Rank l)
    (z : Axes l) : ℝ :=
  ∏ i : Fin l, f (w i) (coordinate i (τ i) z)

private theorem integrable_on_cube {d l : ℕ} {f : Fin d → Plane → ℝ} (hf : BoundedMeasurable f)
    (w : Word d l) (τ : Rank l) :
    IntegrableOn (integrand f w τ) (cube l ×ˢ cube l) volume := by
  obtain ⟨hM, M, _, hbound⟩ := hf
  have hm : Measurable (integrand f w τ) :=
    Finset.measurable_prod _ fun i _ => (hM (w i)).comp (measurable_coordinate i (τ i))
  apply IntegrableOn.of_bound ((cube_compact l).prod (cube_compact l)).measure_lt_top
    hm.aestronglyMeasurable (M ^ l)
  apply ae_of_all
  intro z
  rw [integrand, norm_prod]
  calc
    _ ≤ ∏ _ : Fin l, M :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbound (w i) _)
    _ = _ := by simp

def simplexIntegral {d l : ℕ} (f : Fin d → Plane → ℝ) (w : Word d l) (τ : Rank l) : ℝ :=
  ∫ z in simplex l ×ˢ simplex l, integrand f w τ z

private theorem integrand_ae_eq {d l : ℕ} {f g : Fin d → Plane → ℝ}
    (hfg : ∀ c, f c =ᵐ[volume.restrict UnitSquare] g c) (w : Word d l) (τ : Rank l) :
    integrand f w τ =ᵐ[(volume : Measure (Axes l)).restrict (simplex l ×ˢ simplex l)]
      integrand g w τ := by
  have h (i : Fin l) : ∀ᵐ z ∂(volume : Measure (Axes l)).restrict (simplex l ×ˢ simplex l),
      f (w i) (coordinate i (τ i) z) = g (w i) (coordinate i (τ i) z) := by
    have hmaps : MapsTo (coordinate i (τ i)) (simplex l ×ˢ simplex l) UnitSquare :=
      (coordinate_maps i (τ i)).mono (Set.prod_mono inter_subset_left inter_subset_left) Subset.rfl
    exact ((quasiMeasurePreserving_coordinate i (τ i)).restrict hmaps).ae_eq_comp (hfg (w i))
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact Finset.prod_congr rfl fun i _ => hz i

private theorem simplexIntegral_congr {d l : ℕ} {f g : Fin d → Plane → ℝ}
    (hfg : ∀ c, f c =ᵐ[volume.restrict UnitSquare] g c) (w : Word d l) (τ : Rank l) :
    simplexIntegral f w τ = simplexIntegral g w τ :=
  integral_congr_ae (integrand_ae_eq hfg w τ)

def signature {d k : ℕ} (X : Membrane d) : Array ℝ d k := fun l w τ =>
  if l.val = 0 then 1 else simplexIntegral (mixed X) w τ

def Realizes {d k : ℕ} (s : Array ℝ d k) : Prop :=
  ∃ X : Membrane d, PiecewiseBilinear X ∧ signature X = s

/-- Conjecture 6.10 for the printed shuffle of arXiv:2610.16724v1. -/
def claim : Prop :=
  ∀ (d k : ℕ), 2 ≤ d → ∀ s : Array ℝ d k, Printed s → Realizes s

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation
end

end

section

-- Genuine

open MeasureTheory Set Function
open scoped BigOperators
open D5.S3.Quantum.Transport.MatrixUnitDyson (orderedSimplex)

noncomputable section

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

private theorem simplex3_eq :
    {x : Axis 3 | x ∘ Fin.revPerm ∈ orderedSimplex 3 1} = simplex 3 := by
  ext y
  simp only [mem_ofPred_eq, mem_reversed_orderedSimplex, simplex, cube, mem_inter_iff, mem_pi,
    mem_univ, true_implies]

private abbrev SplitAxis := ℝ × Axis 3

private def splitAxis : Axis 4 ≃ᵐ SplitAxis :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin 4)

private def block : Set (Axis 4) := splitAxis ⁻¹' (UnitInterval ×ˢ simplex 3)

private theorem block_subset_cube : block ⊆ cube 4 := by
  intro x hx
  change x 0 ∈ UnitInterval ∧ (x ∘ (0 : Fin 4).succAbove) ∈ simplex 3 at hx
  intro i _
  exact (Fin.forall_iff_succAbove (P := fun j => x j ∈ UnitInterval) (0 : Fin 4)).mpr
    ⟨hx.1, fun j => hx.2.1 j (mem_univ _)⟩ i

private def regroupTail : Axis 3 × SplitAxis ≃ᵐ ℝ × Axes 3 :=
  MeasurableEquiv.prodAssoc.symm.trans
    (((MeasurableEquiv.prodComm : Axis 3 × ℝ ≃ᵐ ℝ × Axis 3).prodCongr
      (MeasurableEquiv.refl (Axis 3))).trans MeasurableEquiv.prodAssoc)

private def regroup : SplitAxis × SplitAxis ≃ᵐ Plane × Axes 3 :=
  (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl ℝ).prodCongr regroupTail)).trans
    MeasurableEquiv.prodAssoc.symm

private theorem mp_regroup : MeasurePreserving regroup volume volume := by
  have ha : MeasurePreserving
      (MeasurableEquiv.prodAssoc : SplitAxis × SplitAxis ≃ᵐ ℝ × Axis 3 × SplitAxis) :=
    volume_preserving_prodAssoc
  have hb : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (Axis 3 × ℝ) × Axis 3 ≃ᵐ Axis 3 × SplitAxis) :=
    volume_preserving_prodAssoc
  have hc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × Axis 3) × Axis 3 ≃ᵐ ℝ × Axes 3) :=
    volume_preserving_prodAssoc
  have hd : MeasurePreserving
      (MeasurableEquiv.prodAssoc : Plane × Axes 3 ≃ᵐ ℝ × ℝ × Axes 3) :=
    volume_preserving_prodAssoc
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : Axis 3 × ℝ ≃ᵐ ℝ × Axis 3) :=
    Measure.measurePreserving_swap
  have hswap' : MeasurePreserving
      ((MeasurableEquiv.prodComm : Axis 3 × ℝ ≃ᵐ ℝ × Axis 3).prodCongr
        (MeasurableEquiv.refl (Axis 3))) :=
    hswap.prod (MeasurePreserving.id volume)
  have htail : MeasurePreserving regroupTail :=
    (hb.symm _).trans (hswap'.trans hc)
  have hmiddle : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr regroupTail) :=
    (MeasurePreserving.id volume).prod htail
  exact (ha.trans hmiddle).trans (hd.symm _)

private def splitAxes : Axes 4 ≃ᵐ Plane × Axes 3 :=
  (splitAxis.prodCongr splitAxis).trans regroup

private theorem mp_splitAxes : MeasurePreserving splitAxes volume volume := by
  have h : MeasurePreserving splitAxis volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)
  exact (h.prod h).trans mp_regroup

private theorem splitAxes_domain :
    splitAxes ⁻¹' (UnitSquare ×ˢ (simplex 3 ×ˢ simplex 3)) = block ×ˢ block := by
  ext z
  change (z.1 0 ∈ UnitInterval ∧ z.2 0 ∈ UnitInterval) ∧
    ((z.1 ∘ (0 : Fin 4).succAbove) ∈ simplex 3 ∧
     (z.2 ∘ (0 : Fin 4).succAbove) ∈ simplex 3) ↔
    (z.1 0 ∈ UnitInterval ∧ (z.1 ∘ (0 : Fin 4).succAbove) ∈ simplex 3) ∧
    (z.2 0 ∈ UnitInterval ∧ (z.2 ∘ (0 : Fin 4).succAbove) ∈ simplex 3)
  tauto

private theorem simplexIntegral_one {d : ℕ} (f : Fin d → Plane → ℝ) (u : Word d 1) :
    simplexIntegral f u (Equiv.refl _) = ∫ z in UnitSquare, f (u 0) z := by
  let e := (MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).prod (volume_preserving_funUnique (Fin 1) ℝ)
  have hp : e ⁻¹' UnitSquare = simplex 1 ×ˢ simplex 1 := by
    ext z
    change (z.1 0 ∈ UnitInterval ∧ z.2 0 ∈ UnitInterval) ↔
      z.1 ∈ simplex 1 ∧ z.2 ∈ simplex 1
    have h (x : Axis 1) : x ∈ simplex 1 ↔ x 0 ∈ UnitInterval := by
      change ((∀ i : Fin 1, i ∈ (Set.univ : Set (Fin 1)) → x i ∈ UnitInterval) ∧ Monotone x) ↔ _
      refine ⟨fun hx => hx.1 0 (mem_univ _), fun hx => ⟨?_, ?_⟩⟩
      · intro i _
        simpa [Subsingleton.elim i (0 : Fin 1)] using hx
      · intro i j _
        rw [Subsingleton.elim i j]
    rw [h, h]
  have hs : MeasurableSet UnitSquare := measurableSet_Icc.prod measurableSet_Icc
  have hint := (he.restrict_preimage hs).integral_comp' (f (u 0))
  rw [hp] at hint
  change (∫ z : Axes 1 in simplex 1 ×ˢ simplex 1, f (u 0) (z.1 0, z.2 0)) = _ at hint
  simpa [simplexIntegral, integrand, coordinate] using hint

private theorem blockRank_right {m n : ℕ} (α : Rank m) (β : Rank n) (i : Fin n) :
    blockRank α β (Fin.natAdd m i) = Fin.natAdd m (β i) := by
  rw [← finSumFinEquiv_apply_right i]
  simp [blockRank, finSumFinEquiv_apply_right]

private theorem natAdd_one (i : Fin 3) : Fin.natAdd 1 i = (0 : Fin 4).succAbove i :=
  (show ∀ i : Fin 3, Fin.natAdd 1 i = (0 : Fin 4).succAbove i by decide) i

private theorem block_integrand {d : ℕ} (f : Fin d → Plane → ℝ)
    (u : Word d 1) (v : Word d 3) (β : Rank 3) (z : Axes 4) :
    integrand f (Fin.append u v) (blockRank (Equiv.refl _) β) z =
      f (u 0) (splitAxes z).1 * integrand f v β (splitAxes z).2 := by
  unfold integrand
  rw [Fin.prod_univ_add]
  congr 1
  · simp [coordinate, Fin.append_left]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [blockRank_right, Fin.append_right]
    simp only [coordinate, natAdd_one]
    rfl

private theorem block_integral {d : ℕ} (f : Fin d → Plane → ℝ)
    (u : Word d 1) (v : Word d 3) (β : Rank 3) :
    simplexIntegral f u (Equiv.refl _) * simplexIntegral f v β =
      ∫ z in block ×ˢ block, integrand f (Fin.append u v) (blockRank (Equiv.refl _) β) z := by
  rw [simplexIntegral_one]
  unfold simplexIntegral
  rw [← setIntegral_prod_mul]
  have hm : MeasurableSet (UnitSquare ×ˢ (simplex 3 ×ˢ simplex 3)) :=
    (measurableSet_Icc.prod measurableSet_Icc).prod
      ((measurableSet_simplex 3).prod (measurableSet_simplex 3))
  have he := (mp_splitAxes.restrict_preimage hm).integral_comp'
    (fun z : Plane × Axes 3 => f (u 0) z.1 * integrand f v β z.2)
  change (∫ z : Plane × Axes 3 in UnitSquare ×ˢ (simplex 3 ×ˢ simplex 3),
    f (u 0) z.1 * integrand f v β z.2) = _
  simpa only [Function.comp_apply, ← block_integrand, splitAxes_domain] using he.symm

private theorem integrand_reindex {d l : ℕ} (f : Fin d → Plane → ℝ)
    (w : Word d l) (τ π σ : Rank l) (z : Axes l) :
    integrand f w τ (z.1 ∘ π, z.2 ∘ σ) =
      integrand f (w ∘ π.symm) ((π.symm.trans τ).trans σ) z := by
  unfold integrand
  apply Fintype.prod_equiv π
  intro i
  simp [coordinate, Function.comp_apply]

private theorem genuineForRepresentative {d : ℕ} {f : Fin d → Plane → ℝ} (hf : BoundedMeasurable f)
    (u : Word d 1) (v : Word d 3) (β : Rank 3) :
    simplexIntegral f u (Equiv.refl _) * simplexIntegral f v β =
      shuffleSum (simplexIntegral f) u v (blockRank (Equiv.refl _) β) := by
  rw [block_integral, genuineSum_one_three]
  let g := integrand f (Fin.append u v) (blockRank (Equiv.refl _) β)
  have hg : IntegrableOn g (block ×ˢ block) volume :=
    (integrable_on_cube hf _ _).mono_set (Set.prod_mono block_subset_cube block_subset_cube)
  have hh := insertion g
  rw [simplex3_eq] at hh
  have hi := hh hg
  refine hi.trans (Finset.sum_congr rfl fun p _ => ?_)
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change integrand f (Fin.append u v) (blockRank (Equiv.refl _) β)
    (z.1 ∘ insertionRank p.1, z.2 ∘ insertionRank p.2) = _
  exact integrand_reindex _ _ _ _ _ _

private theorem genuineForMembrane {d : ℕ} {X : Membrane d} (hX : PiecewiseBilinear X)
    (u : Word d 1) (v : Word d 3) (β : Rank 3) :
    signature (k := 4) X 1 u (Equiv.refl _) * signature (k := 4) X 3 v β =
      shuffleSum (signature (k := 4) X 4) u v (blockRank (Equiv.refl _) β) := by
  obtain ⟨f, hf, heq⟩ := mixed_representative hX
  have h (l : Fin 5) (hl : l.val ≠ 0) (w : Word d l) (τ : Rank l) :
      signature X l w τ = simplexIntegral f w τ := by
    simp only [signature, hl, ite_false]
    exact simplexIntegral_congr heq w τ
  rw [h 1 (by decide), h 3 (by decide)]
  refine (genuineForRepresentative hf u v β).trans ?_
  unfold shuffleSum
  exact Finset.sum_congr rfl fun p _ => (h 4 (by decide) _ _).symm

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation
end

end

section

-- Certificate

open scoped BigOperators

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

/-- One-line permutation in the one-based decimal notation of the rational table. -/
def rankCode {l : ℕ} (τ : Rank l) : ℕ :=
  (List.ofFn (fun i => (τ i).val + 1)).foldl (fun a j => 10 * a + j) 0

def tableEntry : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | 12 => 7/4
  | 21 => 11/4
  | 123 => 7/12
  | 132 => 1/3
  | 213 => 1/3
  | 231 => 19/12
  | 312 => 7/12
  | 321 => 13/12
  | 1234 => 71/576
  | 1243 => 55/576
  | 1324 => 35/576
  | 1342 => 19/576
  | 1423 => 19/576
  | 1432 => 19/576
  | 2134 => 55/576
  | 2143 => 13/192
  | 2314 => 19/576
  | 2341 => 35/576
  | 2413 => 1/192
  | 2431 => 35/576
  | 3124 => 19/576
  | 3142 => 1/192
  | 3214 => 19/576
  | 3241 => 35/576
  | 3412 => 73/192
  | 3421 => 107/576
  | 4123 => 323/576
  | 4132 => 179/576
  | 4213 => 179/576
  | 4231 => 67/576
  | 4312 => 251/576
  | 4321 => 139/576
  | _ => 0

def rationalWitness : Array ℚ 2 4 := fun _ w τ =>
  if ∀ i, w i = 0 then tableEntry (rankCode τ) else 0

private theorem rationalUnit (w : Word 2 0) (τ : Rank 0) :
    rationalWitness 0 w τ = 1 := by
  have hw : (∀ i, w i = 0) := fun i => i.elim0
  simp [rationalWitness, hw, rankCode, tableEntry]

def oneWord (d l : ℕ) : Word (d+1) l := fun _ => 0

private theorem rationalGenuineSum :
    shuffleSum (rationalWitness 4) (oneWord 1 1) (oneWord 1 3)
      (blockRank (Equiv.refl _) cycle231) = 7/4 := by decide +kernel

private theorem rationalPrintedSum :
    printedRhs rationalWitness 1 3 (by decide) (oneWord 1 1) (oneWord 1 3)
      (Equiv.refl _) cycle231 = 19/4 := by decide +kernel

private def PrintedAt (m n : Fin 5) (h : m.val+n.val ≤ 4) : Prop :=
  ∀ u v α β, rationalWitness m u α * rationalWitness n v β =
    printedRhs rationalWitness m n h u v α β

private theorem printed_1_1 : PrintedAt 1 1 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem printed_1_2 : PrintedAt 1 2 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem printed_2_1 : PrintedAt 2 1 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem printed_1_3 : PrintedAt 1 3 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem printed_2_2 : PrintedAt 2 2 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem printed_3_1 : PrintedAt 3 1 (by decide) := by
  unfold PrintedAt
  decide +kernel

private theorem rationalPrinted : Printed rationalWitness := by
  intro m n h
  by_cases hm : m.val = 0
  · have hzero : m = 0 := Fin.ext hm
    subst m
    intro u v α β
    simp [printedRhs, rationalUnit]
  by_cases hn : n.val = 0
  · have hzero : n = 0 := Fin.ext hn
    subst n
    intro u v α β
    simp [printedRhs, hm, rationalUnit]
  fin_cases m <;> fin_cases n <;>
    first
    | contradiction
    | exact printed_1_1
    | exact printed_1_2
    | exact printed_2_1
    | exact printed_1_3
    | exact printed_2_2
    | exact printed_3_1

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

end

section

-- Refutation

namespace D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

noncomputable def witness : Array ℝ 2 4 := fun l w τ => (rationalWitness l w τ : ℝ)

private theorem witnessPrinted : Printed witness := printed_cast rationalWitness rationalPrinted

private theorem witnessProduct :
    witness 1 (oneWord 1 1) (Equiv.refl _) * witness 3 (oneWord 1 3) cycle231 = 19/4 := by
  have h := rationalPrinted 1 3 (by decide) (oneWord 1 1) (oneWord 1 3)
    (Equiv.refl _) cycle231
  rw [rationalPrintedSum] at h
  have hReal := congrArg (Rat.castHom ℝ) h
  simpa [witness, map_mul] using hReal

private theorem witnessGenuineSum :
    shuffleSum (witness 4) (oneWord 1 1) (oneWord 1 3)
      (blockRank (Equiv.refl _) cycle231) = 7/4 := by
  have h := congrArg (Rat.castHom ℝ) rationalGenuineSum
  simpa [shuffleSum, witness, map_sum] using h

private theorem witnessUnrealizable : ¬ Realizes witness := by
  rintro ⟨X, hX, hsig⟩
  have h := genuineForMembrane hX (oneWord 1 1) (oneWord 1 3) cycle231
  rw [hsig, witnessProduct, witnessGenuineSum] at h
  norm_num at h

/-- The printed shuffle equations admit a normalized array that no membrane realizes. -/
theorem refute_conjecture_6_10_v1 : ¬ claim := by
  intro h
  exact witnessUnrealizable (h 2 4 (by decide) witness witnessPrinted)

end D5.S3.Analytic.MembraneSignatures.AmendolaRiffoSchmitzRefutation

end
