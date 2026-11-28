/- GID: D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine predecessor branches and width of three-state min-plus walks. -/
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61AssignmentGuards
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.Basic

/-!
# Three-state predecessor width

This is the integer geometry of Section 2 of `q61-three-state-single-drift.txt`.
Triples retain coordinate `0` so a predecessor can select it in any column.
For Bob graphs with missing transitions, the update ranges over the actual
sources of each column. For the complete graph it specializes to the canonical
endpoint recurrence, so the affine formula applies to the scores of a legal
Alice walk.
-/

namespace Q61PredecessorWidth

abbrev State := Fin 3
abbrev Triple (R : Type*) := State → R
abbrev Predecessor := State → State

/-- A column selects its source and the source selected by column zero fixes the origin. -/
def reindex {R : Type*} [Sub R] (p : Predecessor) (x : Triple R) : Triple R :=
  fun j => x (p j) - x (p 0)

@[simp] theorem reindex_zero {R : Type*} [AddCommGroup R]
    (p : Predecessor) (x : Triple R) : reindex p x 0 = 0 := by
  simp [reindex]

theorem reindex_id {R : Type*} [AddCommGroup R] {x : Triple R} (hx : x 0 = 0) :
    reindex id x = x := by
  funext j
  simp [reindex, hx]

/-- When `p` acts first and `q` second, `p ∘ q` traces output columns back to the input. -/
theorem reindex_comp {R : Type*} [AddCommGroup R] (p q : Predecessor) :
    (reindex q : Triple R → Triple R) ∘ reindex p = reindex (p ∘ q) := by
  funext x j
  simp only [Function.comp_apply, reindex]
  abel

/-- The second branch reindexes the first branch's offset before adding its own. -/
theorem affine_comp {R : Type*} [AddCommGroup R] (p q : Predecessor)
    (x d e : Triple R) :
    (fun j => reindex q (fun i => reindex p x i + d i) j + e j) =
      fun j => reindex (p ∘ q) x j + (reindex q d j + e j) := by
  funext j
  simp only [reindex, Function.comp_apply]
  abel

/-- The integer reindexings form a finite semigroup under function composition. -/
theorem finite_reindex_semigroup :
    (Set.range (reindex (R := ℤ))).Finite ∧
      ∀ f g : Triple ℤ → Triple ℤ, f ∈ Set.range (reindex (R := ℤ)) →
        g ∈ Set.range (reindex (R := ℤ)) → f ∘ g ∈ Set.range (reindex (R := ℤ)) := by
  refine ⟨Set.finite_range _, ?_⟩
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  exact ⟨q ∘ p, (reindex_comp q p).symm⟩

/-- The branch offset is the difference of its two selected column costs. -/
def offset {R : Type*} [Sub R] (cost : State → State → R) (p : Predecessor) : Triple R :=
  fun j => cost (p j) j - cost (p 0) 0

@[simp] theorem offset_zero {R : Type*} [AddCommGroup R]
    (cost : State → State → R) (p : Predecessor) : offset cost p 0 = 0 := by
  simp [offset]

/-- The finite sources in each column encode the support of the min-plus matrix. -/
structure MinPlusMatrix (R : Type*) where
  cost : Matrix State State R
  sources : State → Finset State
  sources_nonempty : ∀ j, (sources j).Nonempty

namespace MinPlusMatrix

/-- Restrict a matrix of supplied parallel-edge minima to the actual Bob
transitions. Each destination must have an incoming edge. -/
noncomputable def ofGraph {R F : Type*} (Y : Maths.EdgeGraph State F)
    (cost : Matrix State State R) (incoming : ∀ j, ∃ f, Y.target f = j) : MinPlusMatrix R := by
  classical
  refine ⟨cost, fun j => Finset.univ.filter (fun i => ∃ f, Y.source f = i ∧ Y.target f = j), ?_⟩
  intro j
  obtain ⟨f, hf⟩ := incoming j
  exact ⟨Y.source f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, rfl, hf⟩⟩

@[simp] theorem mem_sources_ofGraph {R F : Type*} (Y : Maths.EdgeGraph State F)
    (cost : Matrix State State R) (incoming : ∀ j, ∃ f, Y.target f = j) (i j : State) :
    i ∈ (ofGraph Y cost incoming).sources j ↔ ∃ f, Y.source f = i ∧ Y.target f = j := by
  classical
  simp [ofGraph]

theorem sources_ofGraph_complete {R : Type*} (cost : Matrix State State R)
    (incoming : ∀ j, ∃ f, (MeyerovitchYoungQ61Complete.completeGraph State).target f = j)
    (j : State) :
    (ofGraph (MeyerovitchYoungQ61Complete.completeGraph State) cost incoming).sources j =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  exact (mem_sources_ofGraph _ _ _ i j).2 ⟨(i, j), rfl, rfl⟩

variable {R : Type*} [CommRing R] [LinearOrder R]

def endpointUpdate (M : MinPlusMatrix R) (x : Triple R) : Triple R :=
  fun j => (M.sources j).inf' (M.sources_nonempty j) (fun i => x i + M.cost i j)

/-- When every source is present, the restricted minimum is the repository's
complete Bob update. -/
theorem endpointUpdate_eq_complete [IsStrictOrderedRing R] (M : MinPlusMatrix R)
    (full : ∀ j, M.sources j = Finset.univ) (x : Triple R) :
    M.endpointUpdate x = Q61AssignmentGuards.endpointUpdate M.cost x := by
  rcases M with ⟨cost, sources, nonempty⟩
  have hs : sources = fun _ => Finset.univ := funext full
  subst sources
  rfl

def projectiveUpdate (M : MinPlusMatrix R) (x : Triple R) : Triple R :=
  reindex id (M.endpointUpdate x)

@[simp] theorem projectiveUpdate_zero (M : MinPlusMatrix R) (x : Triple R) :
    M.projectiveUpdate x 0 = 0 := reindex_zero id (M.endpointUpdate x)

/-- Closed column comparisons allow every choice attaining a tied minimum. -/
def ClosedColumnComparisons (M : MinPlusMatrix R) (x : Triple R) (p : Predecessor) : Prop :=
  ∀ j, p j ∈ M.sources j ∧
    ∀ i ∈ M.sources j, x (p j) + M.cost (p j) j ≤ x i + M.cost i j

theorem closedColumnComparisons_iff_attained (M : MinPlusMatrix R) (x : Triple R)
    (p : Predecessor) :
    M.ClosedColumnComparisons x p ↔
      ∀ j, p j ∈ M.sources j ∧ M.endpointUpdate x j = x (p j) + M.cost (p j) j := by
  constructor
  · intro guards j
    obtain ⟨hp, compare⟩ := guards j
    refine ⟨hp, le_antisymm ?_ ?_⟩
    · exact Finset.inf'_le (fun i => x i + M.cost i j) hp
    · exact Finset.le_inf' (M.sources_nonempty j) _ compare
  · intro attained j
    obtain ⟨hp, heq⟩ := attained j
    refine ⟨hp, fun i hi => ?_⟩
    rw [← heq]
    exact Finset.inf'_le (fun k => x k + M.cost k j) hi

theorem exists_closedColumnComparisons (M : MinPlusMatrix R) (x : Triple R) :
    ∃ p : Predecessor, M.ClosedColumnComparisons x p := by
  classical
  have attained (j : State) :
      ∃ i ∈ M.sources j, M.endpointUpdate x j = x i + M.cost i j :=
    Finset.exists_mem_eq_inf' (M.sources_nonempty j) (fun i => x i + M.cost i j)
  choose p hp heq using attained
  exact ⟨p, (M.closedColumnComparisons_iff_attained x p).2 (fun j => ⟨hp j, heq j⟩)⟩

theorem projectiveUpdate_eq_affine (M : MinPlusMatrix R) (x : Triple R) (p : Predecessor)
    (guards : M.ClosedColumnComparisons x p) :
    M.projectiveUpdate x = fun j => reindex p x j + offset M.cost p j := by
  have attained := (M.closedColumnComparisons_iff_attained x p).1 guards
  funext j
  change M.endpointUpdate x j - M.endpointUpdate x 0 = _
  rw [(attained j).2, (attained 0).2]
  unfold reindex offset
  ring

/-- A cost decomposition in `1, α` induces the same predecessor map on each
integer coefficient triple, with the corresponding integer branch offset. -/
theorem projectiveUpdate_coefficients (M : MinPlusMatrix R) (p : Predecessor)
    (α : R) (a q : Triple ℤ) (A B : State → State → ℤ)
    (cost_eq : ∀ i j, i ∈ M.sources j → M.cost i j = (A i j : R) + α * (B i j : R))
    (guards : M.ClosedColumnComparisons (fun j => (a j : R) + α * (q j : R)) p)
    (j : State) :
    M.projectiveUpdate (fun i => (a i : R) + α * (q i : R)) j =
      ((reindex p a j + offset A p j : ℤ) : R) +
        α * ((reindex p q j + offset B p j : ℤ) : R) := by
  rw [M.projectiveUpdate_eq_affine _ p guards]
  simp only [reindex, offset, Int.cast_add, Int.cast_sub]
  rw [cost_eq (p j) j (guards j).1, cost_eq (p 0) 0 (guards 0).1]
  ring

end MinPlusMatrix

/-- On a legal complete-matrix walk, an attained predecessor branch acts on
the endpoint scores of the actual prefix. -/
theorem completeWalk_projective_eq_affine {R V E : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {X : Maths.EdgeGraph V E} {s t : V} (walk : X.Walk s t)
    (e : E) (legal : X.source e = t) (A : E → Matrix State State R)
    (x : Triple R) (p : Predecessor)
    (guards : ∀ j i,
      Q61AssignmentGuards.endpointScores A x walk.edges (p j) + A e (p j) j ≤
        Q61AssignmentGuards.endpointScores A x walk.edges i + A e i j) :
    reindex id (Q61AssignmentGuards.endpointScores A x (walk.concat e legal).edges) =
      fun j => reindex p (Q61AssignmentGuards.endpointScores A x walk.edges) j +
        offset (A e) p j := by
  let M := MinPlusMatrix.ofGraph (MeyerovitchYoungQ61Complete.completeGraph State)
    (A e) (fun j => ⟨(j, j), rfl⟩)
  have full (j : State) : M.sources j = Finset.univ :=
    MinPlusMatrix.sources_ofGraph_complete _ _ j
  let scores := Q61AssignmentGuards.endpointScores A x walk.edges
  have hguard : M.ClosedColumnComparisons scores p := by
    intro j
    refine ⟨?_, fun i _ => guards j i⟩
    rw [full]
    exact Finset.mem_univ _
  have hupdate : M.endpointUpdate scores = Q61AssignmentGuards.endpointUpdate (A e) scores :=
    M.endpointUpdate_eq_complete full scores
  rw [Maths.EdgeGraph.Walk.edges_concat, Q61AssignmentGuards.endpointScores_snoc]
  change reindex id (Q61AssignmentGuards.endpointUpdate (A e) scores) = _
  rw [← hupdate]
  exact M.projectiveUpdate_eq_affine scores p hguard

/-- For a normalized triple this is `max(0, v₁, v₂) - min(0, v₁, v₂)`. -/
def width (v : Triple ℤ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty v - Finset.univ.inf' Finset.univ_nonempty v

theorem sub_le_width (v : Triple ℤ) (i j : State) : v i - v j ≤ width v := by
  unfold width
  exact sub_le_sub (Finset.le_sup' v (Finset.mem_univ i))
    (Finset.inf'_le v (Finset.mem_univ j))

theorem exists_sub_eq_width (v : Triple ℤ) : ∃ i j, v i - v j = width v := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
  refine ⟨i, j, ?_⟩
  unfold width
  rw [hi, hj]

theorem width_le_of_sub_le (v : Triple ℤ) {w : ℤ} (h : ∀ i j, v i - v j ≤ w) :
    width v ≤ w := by
  obtain ⟨i, j, hij⟩ := exists_sub_eq_width v
  rw [← hij]
  exact h i j

theorem width_nonneg (v : Triple ℤ) : 0 ≤ width v := by
  simpa using sub_le_width v 0 0

theorem abs_sub_le_width (v : Triple ℤ) (i j : State) : |v i - v j| ≤ width v := by
  refine abs_le.2 ⟨?_, sub_le_width v i j⟩
  have h := sub_le_width v j i
  omega

theorem width_mul (h : ℤ) (v : Triple ℤ) :
    width (fun j => h * v j) = |h| * width v := by
  apply le_antisymm
  · apply width_le_of_sub_le
    intro i j
    calc
      h * v i - h * v j ≤ |h * v i - h * v j| := le_abs_self _
      _ = |h| * |v i - v j| := by rw [← mul_sub, abs_mul]
      _ ≤ |h| * width v := mul_le_mul_of_nonneg_left (abs_sub_le_width v i j) (abs_nonneg h)
  · obtain ⟨i, j, hij⟩ := exists_sub_eq_width v
    calc
      |h| * width v = |h| * |v i - v j| := by rw [hij, abs_of_nonneg (width_nonneg v)]
      _ = |h * v i - h * v j| := by rw [← mul_sub, abs_mul]
      _ ≤ width (fun j => h * v j) := abs_sub_le_width _ i j

private theorem reindex_sub (p : Predecessor) (v : Triple ℤ) (i j : State) :
    reindex p v i - reindex p v j = v (p i) - v (p j) := by
  unfold reindex
  ring

theorem width_reindex_le (p : Predecessor) (v : Triple ℤ) : width (reindex p v) ≤ width v := by
  apply width_le_of_sub_le
  intro i j
  rw [reindex_sub]
  exact sub_le_width v (p i) (p j)

theorem width_permutation (σ : Equiv.Perm State) (v : Triple ℤ) :
    width (reindex σ v) = width v := by
  refine le_antisymm (width_reindex_le σ v) ?_
  obtain ⟨i, j, hij⟩ := exists_sub_eq_width v
  have h := sub_le_width (reindex σ v) (σ.symm i) (σ.symm j)
  rw [reindex_sub] at h
  simpa only [Equiv.apply_symm_apply, hij] using h

theorem permutation_inverse (σ : Equiv.Perm State) (v : Triple ℤ) (hv : v 0 = 0) :
    reindex σ.symm (reindex σ v) = v := by
  calc
    reindex σ.symm (reindex σ v) = reindex id v := by
      funext j
      simp only [reindex, Equiv.apply_symm_apply, id_eq]
      abel
    _ = v := reindex_id hv

/-- Bézout primitivity of the two free integer coordinates. -/
def Primitive (v : Triple ℤ) : Prop := ∃ a b : ℤ, a * v 1 + b * v 2 = 1

theorem primitive_ne_zero {v : Triple ℤ} (hv : Primitive v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := hv
  simp at hab

theorem one_le_width_of_primitive {v : Triple ℤ} (hv₀ : v 0 = 0) (hv : Primitive v) :
    1 ≤ width v := by
  by_contra h
  apply primitive_ne_zero hv
  funext j
  have hmax := sub_le_width v j 0
  have hmin := sub_le_width v 0 j
  rw [hv₀] at hmax hmin
  change v j = 0
  omega

theorem primitive_of_width_one {v : Triple ℤ} (hv₀ : v 0 = 0) (hw : width v = 1) :
    Primitive v := by
  have coordinate (i : State) : ∃ a b : ℤ, v i = a * v 1 + b * v 2 := by
    fin_cases i
    · exact ⟨0, 0, by simpa using hv₀⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  obtain ⟨i, j, hij⟩ := exists_sub_eq_width v
  obtain ⟨a, b, hi⟩ := coordinate i
  obtain ⟨c, d, hj⟩ := coordinate j
  refine ⟨a - c, b - d, ?_⟩
  calc
    (a - c) * v 1 + (b - d) * v 2 = v i - v j := by
      rw [hi, hj]
      ring
    _ = 1 := hij.trans hw

private theorem primitive_factor {v u : Triple ℤ} {h : ℤ} (hv : Primitive v)
    (heq : v = fun j => h * u j) : |h| = 1 := by
  obtain ⟨a, b, hab⟩ := hv
  rw [heq] at hab
  have hone : h * (a * u 1 + b * u 2) = 1 := by
    calc
      h * (a * u 1 + b * u 2) = a * (h * u 1) + b * (h * u 2) := by ring
      _ = 1 := hab
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hone with hpos | hneg
  · simp [hpos]
  · simp [hneg]

theorem permutation_aligned_multiplier (σ : Equiv.Perm State) {v w : Triple ℤ} {h : ℤ}
    (hv₀ : v 0 = 0) (hv : Primitive v)
    (halign : reindex σ v = fun j => h * w j) : |h| = 1 := by
  apply primitive_factor hv (u := reindex σ.symm w)
  calc
    v = reindex σ.symm (reindex σ v) := (permutation_inverse σ v hv₀).symm
    _ = fun j => h * reindex σ.symm w j := by
      rw [halign]
      funext j
      unfold reindex
      ring

/-- A repeated predecessor leaves at most two source indices among the three columns. -/
private theorem two_predecessor_indices (p : Predecessor) (hp : ¬ Function.Injective p) :
    ∃ r : State, ∀ j, p j = p 0 ∨ p j = p r := by
  by_cases h₁ : p 1 = p 0
  · refine ⟨2, ?_⟩
    intro j
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inl h₁
    · exact Or.inr rfl
  by_cases h₂ : p 2 = p 0
  · refine ⟨1, ?_⟩
    intro j
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl h₂
  by_cases h₂₁ : p 2 = p 1
  · refine ⟨1, ?_⟩
    intro j
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr h₂₁
  exfalso
  apply hp
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact (h₁ hij).elim
    | exact (h₁ hij.symm).elim
    | exact (h₂ hij).elim
    | exact (h₂ hij.symm).elim
    | exact (h₂₁ hij).elim
    | exact (h₂₁ hij.symm).elim

theorem noninjective_two_levels (p : Predecessor) (hp : ¬ Function.Injective p)
    (v : Triple ℤ) : ∃ r : State, ∀ j, reindex p v j = 0 ∨ reindex p v j = reindex p v r := by
  obtain ⟨r, hr⟩ := two_predecessor_indices p hp
  refine ⟨r, fun j => ?_⟩
  rcases hr j with hj | hj
  · left
    simp [reindex, hj]
  · right
    simp [reindex, hj]

private theorem factor_two_levels {v : Triple ℤ} {d : ℤ}
    (hv₀ : v 0 = 0) (hv : v ≠ 0) (levels : ∀ j, v j = 0 ∨ v j = d) :
    ∃ u : Triple ℤ, u 0 = 0 ∧ (∀ j, u j = 0 ∨ u j = 1) ∧
      width u = 1 ∧ v = fun j => d * u j := by
  have hex : ∃ j, v j ≠ 0 := by
    by_contra! hall
    apply hv
    funext j
    exact hall j
  obtain ⟨i, hi⟩ := hex
  let u : Triple ℤ := fun j => if v j = 0 then 0 else 1
  have hu₀ : u 0 = 0 := by simp [u, hv₀]
  have hui : u i = 1 := by simp [u, hi]
  have hu (j : State) : u j = 0 ∨ u j = 1 := by
    by_cases hj : v j = 0 <;> simp [u, hj]
  refine ⟨u, hu₀, hu, le_antisymm ?_ ?_, ?_⟩
  · apply width_le_of_sub_le
    intro j k
    rcases hu j with hj | hj <;> rcases hu k with hk | hk <;> rw [hj, hk] <;> decide
  · simpa only [hui, hu₀, sub_zero] using sub_le_width u i 0
  · funext j
    by_cases hj : v j = 0
    · simp [u, hj]
    · have hd := (levels j).resolve_left hj
      simpa [u, hj] using hd

/-- A nonzero repeated-predecessor output is a signed multiple of a normalized
primitive direction with levels zero and one. The multiplier is a selected input difference. -/
theorem noninjective_primitive_direction (p : Predecessor) (hp : ¬ Function.Injective p)
    (v : Triple ℤ) (hv : reindex p v ≠ 0) :
    ∃ (r : State) (u : Triple ℤ), u 0 = 0 ∧ (∀ j, u j = 0 ∨ u j = 1) ∧
      Primitive u ∧ width u = 1 ∧
      reindex p v = (fun j => (v (p r) - v (p 0)) * u j) ∧
      1 ≤ |v (p r) - v (p 0)| ∧ |v (p r) - v (p 0)| ≤ width v := by
  obtain ⟨r, hr⟩ := noninjective_two_levels p hp v
  obtain ⟨u, hu₀, hu, hw, hfactor⟩ := factor_two_levels (reindex_zero p v) hv hr
  change reindex p v = (fun j => (v (p r) - v (p 0)) * u j) at hfactor
  have hh : v (p r) - v (p 0) ≠ 0 := by
    intro hz
    apply hv
    rw [hfactor]
    funext j
    simp [hz]
  have hpos : 0 < |v (p r) - v (p 0)| := abs_pos.mpr hh
  exact ⟨r, u, hu₀, hu, primitive_of_width_one hu₀ hw, hw, hfactor,
    by omega, abs_sub_le_width v (p r) (p 0)⟩

/-- The width-one bound also holds for the primitive direction of any aligned target chart. -/
theorem noninjective_aligned_width (p : Predecessor) (hp : ¬ Function.Injective p)
    {v w : Triple ℤ} {h : ℤ} (hw₀ : w 0 = 0) (hw : Primitive w) (hh : h ≠ 0)
    (halign : reindex p v = fun j => h * w j) :
    width w = 1 ∧ 1 ≤ |h| ∧ |h| ≤ width v := by
  obtain ⟨r, hr⟩ := noninjective_two_levels p hp v
  have levels (j : State) : w j = 0 ∨ w j = w r := by
    have hj := hr j
    rw [halign] at hj
    rcases hj with hz | heq
    · left
      apply mul_left_cancel₀ hh
      simpa only [mul_zero] using hz
    · exact Or.inr (mul_left_cancel₀ hh heq)
  obtain ⟨u, _, _, hu, heq⟩ := factor_two_levels hw₀ (primitive_ne_zero hw) levels
  have hwidth : width w = 1 := by
    rw [heq, width_mul, primitive_factor hw heq, hu, one_mul]
  have hbound := width_reindex_le p v
  rw [halign, width_mul, hwidth, mul_one] at hbound
  have hpos : 0 < |h| := abs_pos.mpr hh
  exact ⟨hwidth, by omega, hbound⟩

structure CoefficientLine where
  base : Triple ℤ
  direction : Triple ℤ
  base_zero : base 0 = 0
  direction_zero : direction 0 = 0
  direction_primitive : Primitive direction

def CoefficientLine.coefficient (L : CoefficientLine) (n : ℤ) : Triple ℤ :=
  fun j => L.base j + n * L.direction j

@[simp] theorem CoefficientLine.coefficient_zero (L : CoefficientLine) (n : ℤ) :
    L.coefficient n 0 = 0 := by
  simp [CoefficientLine.coefficient, L.base_zero, L.direction_zero]

/-- An ordinary chart transition aligns the affine coefficient lines with a
nonzero multiplier. The vector `b` is the irrational coefficient of the branch offset. -/
structure Aligned (p : Predecessor) (b : Triple ℤ) (L L' : CoefficientLine) (h c : ℤ) : Prop where
  multiplier_ne_zero : h ≠ 0
  base_eq : (fun j => reindex p L.base j + b j) = fun j => L'.base j + c * L'.direction j
  direction_eq : reindex p L.direction = fun j => h * L'.direction j

theorem Aligned.coefficient_eq {p b L L' h c} (step : Aligned p b L L' h c) (n : ℤ) :
    (fun j => reindex p (L.coefficient n) j + b j) = L'.coefficient (h * n + c) := by
  funext j
  have base_eq : reindex p L.base j + b j = L'.base j + c * L'.direction j :=
    congrFun step.base_eq j
  have direction_eq : reindex p L.direction j = h * L'.direction j :=
    congrFun step.direction_eq j
  calc
    reindex p (L.coefficient n) j + b j =
        (reindex p L.base j + b j) + n * reindex p L.direction j := by
      unfold reindex CoefficientLine.coefficient
      ring
    _ = L'.coefficient (h * n + c) j := by
      rw [base_eq, direction_eq]
      unfold CoefficientLine.coefficient
      ring

/-- On the attained branch, an aligned update sends the line parameter to `h * n + c`. -/
theorem MinPlusMatrix.projectiveUpdate_aligned {R : Type*} [CommRing R] [LinearOrder R]
    (M : MinPlusMatrix R) (p : Predecessor) (α : R) (a : Triple ℤ)
    (A B : State → State → ℤ)
    (cost_eq : ∀ i j, i ∈ M.sources j → M.cost i j = (A i j : R) + α * (B i j : R))
    {L L' : CoefficientLine} {h c : ℤ} (n : ℤ)
    (guards : M.ClosedColumnComparisons (fun j => (a j : R) + α * (L.coefficient n j : R)) p)
    (step : Aligned p (offset B p) L L' h c) (j : State) :
    M.projectiveUpdate (fun i => (a i : R) + α * (L.coefficient n i : R)) j =
      ((reindex p a j + offset A p j : ℤ) : R) +
        α * (L'.coefficient (h * n + c) j : R) := by
  have hcoeff : reindex p (L.coefficient n) j + offset B p j =
      L'.coefficient (h * n + c) j := congrFun (step.coefficient_eq n) j
  rw [M.projectiveUpdate_coefficients p α a (L.coefficient n) A B cost_eq guards j, hcoeff]

theorem Aligned.permutation_width {p b L L' h c} (step : Aligned p b L L' h c)
    (hp : Function.Injective p) : width L'.direction = width L.direction ∧ |h| = 1 := by
  let σ : Equiv.Perm State := Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩
  have hdir : reindex σ L.direction = fun j => h * L'.direction j := step.direction_eq
  have hmul := permutation_aligned_multiplier σ L.direction_zero L.direction_primitive hdir
  have hw := width_permutation σ L.direction
  rw [hdir, width_mul, hmul, one_mul] at hw
  exact ⟨hw, hmul⟩

theorem Aligned.noninjective_width {p b L L' h c} (step : Aligned p b L L' h c)
    (hp : ¬ Function.Injective p) : width L'.direction = 1 ∧ 1 ≤ |h| ∧ |h| ≤ width L.direction :=
  noninjective_aligned_width p hp L'.direction_zero L'.direction_primitive
    step.multiplier_ne_zero step.direction_eq

theorem Aligned.width_eq_or_one {p b L L' h c} (step : Aligned p b L L' h c) :
    width L'.direction = width L.direction ∨ width L'.direction = 1 := by
  by_cases hp : Function.Injective p
  · exact Or.inl (step.permutation_width hp).1
  · exact Or.inr (step.noninjective_width hp).1

theorem Aligned.width_le {p b L L' h c} (step : Aligned p b L L' h c) :
    width L'.direction ≤ width L.direction := by
  rcases step.width_eq_or_one with heq | hone
  · exact heq.le
  · rw [hone]
    exact one_le_width_of_primitive L.direction_zero L.direction_primitive

theorem Aligned.width_one {p b L L' h c} (step : Aligned p b L L' h c)
    (hw : width L.direction = 1) : width L'.direction = 1 ∧ |h| = 1 := by
  by_cases hp : Function.Injective p
  · obtain ⟨hwidth, hmul⟩ := step.permutation_width hp
    exact ⟨hwidth.trans hw, hmul⟩
  · obtain ⟨hwidth, hlo, hhi⟩ := step.noninjective_width hp
    exact ⟨hwidth, le_antisymm (hhi.trans_eq hw) hlo⟩

/-- Every segment of ordinary aligned transitions has at most one strict width drop. -/
theorem alignedPath_at_most_one_drop (L : ℕ → CoefficientLine) (length : ℕ)
    (steps : ∀ i < length, ∃ p b h c, Aligned p b (L i) (L (i + 1)) h c)
    {i j : ℕ} (hi : i < length) (hj : j < length)
    (drop_i : width (L (i + 1)).direction < width (L i).direction)
    (drop_j : width (L (j + 1)).direction < width (L j).direction) : i = j := by
  have mono (a b : ℕ) (hab : a ≤ b) :
      b ≤ length → width (L b).direction ≤ width (L a).direction := by
    induction b, hab using Nat.le_induction with
    | base =>
      intro _
      exact le_rfl
    | succ k _ ih =>
      intro hb
      obtain ⟨p, bₖ, h, c, step⟩ := steps k (by omega)
      exact step.width_le.trans (ih (by omega))
  have no_later_drop (a b : ℕ) (hab : a < b) (hb : b < length)
      (ha_drop : width (L (a + 1)).direction < width (L a).direction)
      (hb_drop : width (L (b + 1)).direction < width (L b).direction) : False := by
    obtain ⟨p, b₀, h, c, step⟩ := steps a (by omega)
    have ha : width (L (a + 1)).direction = 1 :=
      step.width_eq_or_one.resolve_left (ne_of_lt ha_drop)
    have hle := mono (a + 1) b (by omega) (by omega)
    have hmin := one_le_width_of_primitive (L (b + 1)).direction_zero
      (L (b + 1)).direction_primitive
    omega
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (no_later_drop i j hij hj drop_i drop_j).elim
  · exact hij
  · exact (no_later_drop j i hji hi drop_j drop_i).elim

end Q61PredecessorWidth
