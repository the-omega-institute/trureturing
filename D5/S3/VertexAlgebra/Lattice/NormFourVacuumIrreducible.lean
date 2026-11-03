/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumIrreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irreducibility of the actual cyclic norm-four Virasoro vacuum representation. -/

import D5.S3.VertexAlgebra.Lattice.NormFourHighestWeight
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The actual norm-four cyclic Virasoro vacuum representation is irreducible.
Negative words may vanish or be dependent. Finite products of the actual L0
minus distinct scalar weights recover invariant-subspace components, without
an ambient grading, PBW, positivity or an eigenbasis assumption. The norm-four
state retains its Dong-Mason-Zhu / Shimakura attribution, and the lattice and
residue calculus retain their Bakalov-Kac and Carnahan / Matsuo-Nagatomo attribution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction NormFourVirasoroVector
open scoped BigOperators VertexOperator

noncomputable section

private def word (D : LatticeData) (a : Charge D) (s : ℂ) :
    List ℕ → Carrier D
  | [] => vacuum D
  | k :: w => mode D a s (-((k : ℤ) + 1)) (word D a s w)

private def wordGrade : List ℕ → ℕ
  | [] => 0
  | k :: w => (k + 1) + wordGrade w

/-- Span of all finite words of the actual L_{-(k+1)} on vacuum. -/
def vacuumDescendants (D : LatticeData) (a : Charge D) (s : ℂ) :
    Submodule ℂ (Carrier D) :=
  Submodule.span ℂ (Set.range (word D a s))

private theorem word_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : List ℕ) : word D a s w ∈ vacuumDescendants D a s :=
  Submodule.subset_span ⟨w, rfl⟩

private theorem negative_closed (D : LatticeData) (a : Charge D) (s : ℂ)
    (k : ℕ) (v : Carrier D) (hv : v ∈ vacuumDescendants D a s) :
    mode D a s (-((k : ℤ) + 1)) v ∈ vacuumDescendants D a s := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      exact word_mem D a s (k :: w)
  | zero => simp
  | add v u _ _ hv hu => simpa only [map_add] using
      (vacuumDescendants D a s).add_mem hv hu
  | smul c v _ hv => simpa only [map_smul] using
      (vacuumDescendants D a s).smul_mem c hv

-- Evaluated ACTUAL relation, with the central term retained exactly.
private theorem commute_action (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (m n : ℤ) (v : Carrier D) :
    mode D a s m (mode D a s n v) =
      mode D a s n (mode D a s m v) +
        ((m : ℂ) - (n : ℂ)) • mode D a s (m + n) v +
        (if m + n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) • v else 0) := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (virasoro_commutator D a ha s hs m n)
  split_ifs at h ⊢ with hmn <;>
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at h
  all_goals
    calc
      _ = mode D a s n (mode D a s m v) +
          (mode D a s m (mode D a s n v) -
            mode D a s n (mode D a s m v)) := by abel
      _ = _ := by rw [h]; abel

-- Induction is on the entire negative word, uniformly in ALL integer m.
-- The base covers nonnegative modes by creativity and every negative integer
-- by Int.negSucc. In the step both m and m-(k+1) act on the shorter word.
private theorem mode_word_mem (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : List ℕ) :
    ∀ m : ℤ, mode D a s m (word D a s w) ∈ vacuumDescendants D a s := by
  induction w with
  | nil =>
      intro m
      cases m with
      | ofNat n =>
          have hz : mode D a s (n : ℤ) (vacuum D) = 0 :=
            stateField_creativity D (vector D a s) ((n : ℤ) + 1) (by omega)
          change mode D a s (n : ℤ) (vacuum D) ∈ vacuumDescendants D a s
          rw [hz]
          exact (vacuumDescendants D a s).zero_mem
      | negSucc k =>
          have index : Int.negSucc k = -((k : ℤ) + 1) := by omega
          rw [index]
          exact word_mem D a s [k]
  | cons k w ih =>
      intro m
      change mode D a s m
        (mode D a s (-((k : ℤ) + 1)) (word D a s w)) ∈ _
      rw [commute_action D a ha s hs]
      apply (vacuumDescendants D a s).add_mem
      · exact (vacuumDescendants D a s).add_mem
          (negative_closed D a s k _ (ih m))
          ((vacuumDescendants D a s).smul_mem _ (ih _))
      · split_ifs
        · exact (vacuumDescendants D a s).smul_mem _ (word_mem D a s w)
        · exact (vacuumDescendants D a s).zero_mem

private theorem all_modes_closed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (m : ℤ) (v : Carrier D) (hv : v ∈ vacuumDescendants D a s) :
    mode D a s m v ∈ vacuumDescendants D a s := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      exact mode_word_mem D a ha s hs w m
  | zero => simp
  | add v u _ _ hv hu => simpa only [map_add] using
      (vacuumDescendants D a s).add_mem hv hu
  | smul c v _ hv => simpa only [map_smul] using
      (vacuumDescendants D a s).smul_mem c hv

/-- Actual restricted modes; closure is proved above and consumed here. -/
def restrictedMode (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m : ℤ) :
    Module.End ℂ (vacuumDescendants D a s) :=
  (mode D a s m).restrict (all_modes_closed D a ha s hs m)

private theorem eigen_shift (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (h : ℂ) (v : Carrier D) (hv : mode D a s 0 v = h • v) (m : ℤ) :
    mode D a s 0 (mode D a s m v) =
      (h - (m : ℂ)) • mode D a s m v := by
  have comm := commute_action D a ha s hs 0 m v
  have central :
      (if (0 : ℤ) + m = 0 then
        ((((0 : ℤ) : ℂ)^3 - ((0 : ℤ) : ℂ)) / 24) • v else 0) = 0 := by
    split_ifs <;> norm_num
  rw [central, add_zero, zero_add, hv, map_smul] at comm
  rw [comm]
  push_cast
  module

private theorem word_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (w : List ℕ) :
    mode D a s 0 (word D a s w) = (wordGrade w : ℂ) • word D a s w := by
  induction w with
  | nil =>
      simpa only [word, wordGrade, Nat.cast_zero, zero_smul, mode, zero_add] using
        stateField_creativity D (vector D a s) 1 (by omega)
  | cons k w ih =>
      have step := eigen_shift D a ha s hs (wordGrade w : ℂ)
        (word D a s w) ih (-((k : ℤ) + 1))
      change mode D a s 0
        (mode D a s (-((k : ℤ) + 1)) (word D a s w)) = _
      rw [step]
      congr 1
      simp only [wordGrade, Nat.cast_add, Nat.cast_one, Int.cast_neg, Int.cast_add,
        Int.cast_natCast, Int.cast_one]
      ring

private def gradeSpace (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) :
    Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {v | ∃ w, wordGrade w = n ∧ word D a s w = v}

private theorem grade_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (v : Carrier D) (hv : v ∈ gradeSpace D a s n) :
    mode D a s 0 v = (n : ℂ) • v := by
  have le : gradeSpace D a s n ≤ (mode D a s 0).eigenspace (n : ℂ) := by
    apply Submodule.span_le.mpr
    rintro u ⟨w, hw, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [hw] using word_eigen D a ha s hs w
  exact Module.End.mem_eigenspace_iff.mp (le hv)

private theorem grade_zero (D : LatticeData) (a : Charge D) (s : ℂ) :
    gradeSpace D a s 0 = Submodule.span ℂ {vacuum D} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨w, hw, rfl⟩
    have empty : w = [] := by
      cases w with
      | nil => rfl
      | cons k w => simp only [wordGrade] at hw; omega
    subst w
    exact Submodule.subset_span (by simp [word])
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = vacuum D)
    exact Submodule.subset_span ⟨[], rfl, rfl⟩

private def assemble (D : LatticeData) : (ℕ →₀ Carrier D) →ₗ[ℂ] Carrier D :=
  Finsupp.lsum ℂ (fun _ : ℕ => (LinearMap.id : Module.End ℂ (Carrier D)))

-- Finite homogeneous expansion is DERIVED from word-span membership.
private theorem decompose (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (hv : v ∈ vacuumDescendants D a s) :
    ∃ f : ℕ →₀ Carrier D, assemble D f = v ∧
      ∀ n, f n ∈ gradeSpace D a s n := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      refine ⟨Finsupp.single (wordGrade w) (word D a s w), ?_, ?_⟩
      · simp [assemble, Finsupp.lsum_single]
      · intro n
        by_cases hn : wordGrade w = n
        · subst n
          have hw : word D a s w ∈ gradeSpace D a s (wordGrade w) :=
            Submodule.subset_span ⟨w, rfl, rfl⟩
          simpa using hw
        · simp [hn]
  | zero => exact ⟨0, map_zero _, fun n => by simp⟩
  | add v u _ _ hv hu =>
      obtain ⟨f, hf, hfg⟩ := hv
      obtain ⟨g, hg, hgg⟩ := hu
      refine ⟨f + g, by rw [map_add, hf, hg], fun n => ?_⟩
      exact (gradeSpace D a s n).add_mem (hfg n) (hgg n)
  | smul c v _ hv =>
      obtain ⟨f, hf, hfg⟩ := hv
      refine ⟨c • f, by rw [map_smul, hf], fun n => ?_⟩
      exact (gradeSpace D a s n).smul_mem c (hfg n)

-- cut l is the evaluation of the finite polynomial ∏_{j in l} (X-j).
-- A list fixes multiplication order, avoiding any artificial commutative
-- multiplication instance on the algebra of actual endomorphisms.
private def cut (D : LatticeData) (a : Charge D) (s : ℂ) :
    List ℕ → Module.End ℂ (Carrier D)
  | [] => 1
  | k :: l => (mode D a s 0 - (k : ℂ) • 1) * cut D a s l

private def cutValue (l : List ℕ) (h : ℂ) : ℂ :=
  (l.map (fun k : ℕ => h - (k : ℂ))).prod

private theorem cut_eigen (D : LatticeData) (a : Charge D) (s : ℂ)
    (l : List ℕ) (h : ℂ) (v : Carrier D)
    (hv : mode D a s 0 v = h • v) :
    cut D a s l v = cutValue l h • v := by
  induction l with
  | nil => simp [cut, cutValue]
  | cons k l ih =>
      simp only [cut, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, hv,
        cutValue, List.map_cons, List.prod_cons]
      module

private theorem cut_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (W : Submodule ℂ (Carrier D))
    (stable : ∀ v, v ∈ W → mode D a s 0 v ∈ W)
    (l : List ℕ) (v : Carrier D) (hv : v ∈ W) : cut D a s l v ∈ W := by
  induction l with
  | nil => simpa [cut] using hv
  | cons k l ih =>
      simpa only [cut, Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply] using
        W.sub_mem (stable _ ih) (W.smul_mem (k : ℂ) ih)

private theorem cutValue_zero (l : List ℕ) (k : ℕ) (hk : k ∈ l) :
    cutValue l (k : ℂ) = 0 := by
  revert hk
  induction l with
  | nil => simp
  | cons j l ih =>
      intro hk
      rcases List.mem_cons.mp hk with hkj | hk
      · subst j
        simp [cutValue]
      · change ((k : ℂ) - (j : ℂ)) * cutValue l (k : ℂ) = 0
        rw [ih hk, mul_zero]

private theorem cutValue_ne_zero (l : List ℕ) (n : ℕ) (hn : n ∉ l) :
    cutValue l (n : ℂ) ≠ 0 := by
  revert hn
  induction l with
  | nil => simp [cutValue]
  | cons k l ih =>
      intro hn
      simp only [List.mem_cons, not_or] at hn
      change ((n : ℂ) - (k : ℂ)) * cutValue l (n : ℂ) ≠ 0
      exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hn.1)) (ih hn.2)

-- A finite distinct-weight polynomial isolates each component, without an
-- assumed decomposition theorem for invariant subspaces.
private theorem projection_identity (D : LatticeData) (a : Charge D) (s : ℂ)
    (f : ℕ →₀ Carrier D)
    (eigen : ∀ n, mode D a s 0 (f n) = (n : ℂ) • f n)
    (n : ℕ) (hn : n ∈ f.support) :
    cut D a s (f.support.erase n).toList (assemble D f) =
      cutValue (f.support.erase n).toList (n : ℂ) • f n := by
  change cut D a s (f.support.erase n).toList
    (∑ k ∈ f.support, f k) = _
  rw [map_sum]
  calc
    _ = ∑ k ∈ f.support,
        cutValue (f.support.erase n).toList (k : ℂ) • f k := by
          apply Finset.sum_congr rfl
          intro k _
          exact cut_eigen D a s _ _ _ (eigen k)
    _ = _ := by
      apply Finset.sum_eq_single n
      · intro k hk hkn
        rw [cutValue_zero _ k (by simpa using Finset.mem_erase.mpr ⟨hkn, hk⟩),
          zero_smul]
      · intro hn'
        exact (hn' hn).elim

private theorem components_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (f : ℕ →₀ Carrier D)
    (eigen : ∀ n, mode D a s 0 (f n) = (n : ℂ) • f n)
    (W : Submodule ℂ (Carrier D))
    (stable : ∀ v, v ∈ W → mode D a s 0 v ∈ W)
    (hf : assemble D f ∈ W) : ∀ n, f n ∈ W := by
  intro n
  by_cases hn : n ∈ f.support
  · have hc : cutValue (f.support.erase n).toList (n : ℂ) ≠ 0 :=
      cutValue_ne_zero _ n (by simp)
    have projected := cut_mem D a s W stable (f.support.erase n).toList _ hf
    rw [projection_identity D a s f eigen n hn] at projected
    have recovered := W.smul_mem
      (cutValue (f.support.erase n).toList (n : ℂ))⁻¹ projected
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using recovered
  · rw [Finsupp.notMem_support_iff.mp hn]
    exact W.zero_mem

-- Any NONZERO actual eigenvector in the word span has a natural grade and
-- belongs to that grade's actual word span. This also excludes all negative
-- result weights, without any separate ambient positivity assumption.
private theorem eigen_in_grade (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (h : ℂ) (v : Carrier D) (hv : v ∈ vacuumDescendants D a s)
    (nonzero : v ≠ 0) (eigen : mode D a s 0 v = h • v) :
    ∃ n : ℕ, v ∈ gradeSpace D a s n ∧ h = (n : ℂ) := by
  obtain ⟨f, hf, hfg⟩ := decompose D a s v hv
  have feigen := fun n => grade_eigen D a ha s hs n (f n) (hfg n)
  have same : ∀ n, f n ≠ 0 → (n : ℂ) = h := by
    let E := (mode D a s 0).eigenspace h
    have invariant : ∀ x, x ∈ E → mode D a s 0 x ∈ E := by
      intro x hx
      apply Module.End.mem_eigenspace_iff.mpr
      rw [Module.End.mem_eigenspace_iff] at hx
      calc
        mode D a s 0 (mode D a s 0 x) = mode D a s 0 (h • x) :=
          congrArg (mode D a s 0) hx
        _ = h • mode D a s 0 x := map_smul (mode D a s 0) h x
    have fE : ∀ n, f n ∈ E := components_mem D a s f feigen E invariant
      (by rw [hf]; exact Module.End.mem_eigenspace_iff.mpr eigen)
    intro n hn
    have he := Module.End.mem_eigenspace_iff.mp (fE n)
    have hz : ((n : ℂ) - h) • f n = 0 := by
      rw [sub_smul, ← feigen n, he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)
  have exists_nonzero : ∃ n, f n ≠ 0 := by
    by_contra! hzero
    have fzero : f = 0 := Finsupp.ext hzero
    apply nonzero
    rw [← hf, fzero, map_zero]
  obtain ⟨n, hn⟩ := exists_nonzero
  refine ⟨n, ?_, (same n hn).symm⟩
  rw [← hf]
  change (∑ k ∈ f.support, f k) ∈ gradeSpace D a s n
  apply Submodule.sum_mem
  intro k _
  by_cases hk : f k = 0
  · rw [hk]; exact (gradeSpace D a s n).zero_mem
  · have hkn : k = n := by exact_mod_cast (same k hk).trans (same n hn).symm
    simpa only [hkn] using hfg k

/-- The genuine cyclic vacuum representation of the actual
norm-four lattice Virasoro modes is irreducible. All integer restricted modes
occur in the invariance condition. The sole hypotheses concern D, a and s;
the accepted highest-weight theorem is imported, not assumed as a parameter. -/
theorem vacuum_descendants_irreducible (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (U : Submodule ℂ (vacuumDescendants D a s))
    (invariant : ∀ (m : ℤ) (v : vacuumDescendants D a s),
      v ∈ U → restrictedMode D a ha s hs m v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  let W : Submodule ℂ (Carrier D) :=
    U.map (vacuumDescendants D a s).subtype
  have Wle : W ≤ vacuumDescendants D a s := by
    rintro v ⟨u, _, rfl⟩
    exact u.property
  have stable : ∀ (m : ℤ) (v : Carrier D), v ∈ W → mode D a s m v ∈ W := by
    rintro m v ⟨u, hu, rfl⟩
    exact ⟨restrictedMode D a ha s hs m u, invariant m u hu, rfl⟩
  have some_vector : ∃ u : vacuumDescendants D a s, u ∈ U ∧ (u : Carrier D) ≠ 0 := by
    by_contra! hz
    apply hbot
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    exact Subtype.ext (hz u hu)
  obtain ⟨u, hu, hunz⟩ := some_vector
  have huW : (u : Carrier D) ∈ W := ⟨u, hu, rfl⟩
  let P : ℕ → Prop := fun n =>
    ∃ v : Carrier D, v ∈ W ∧ v ∈ gradeSpace D a s n ∧ v ≠ 0
  have some_grade : ∃ n, P n := by
    obtain ⟨f, hf, hfg⟩ := decompose D a s u u.property
    have feigen := fun n => grade_eigen D a ha s hs n (f n) (hfg n)
    have fW := components_mem D a s f feigen W (stable 0) (by rw [hf]; exact huW)
    have hn : ∃ n, f n ≠ 0 := by
      by_contra! hz
      apply hunz
      rw [← hf, show f = 0 from Finsupp.ext hz, map_zero]
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, f n, fW n, hfg n, hn⟩
  let n : ℕ := Nat.find some_grade
  obtain ⟨v, hvW, hvG, hvnz⟩ := Nat.find_spec some_grade
  have minimal : ∀ j, P j → n ≤ j := fun j hj => Nat.find_min' some_grade hj
  have veigen := grade_eigen D a ha s hs n v hvG
  have positive : ∀ m : ℤ, 0 < m → mode D a s m v = 0 := by
    intro m hm
    by_contra hnz
    obtain ⟨j, hjG, hjweight⟩ := eigen_in_grade D a ha s hs
      ((n : ℂ) - (m : ℂ)) (mode D a s m v)
      (Wle (stable m v hvW)) hnz (eigen_shift D a ha s hs _ v veigen m)
    have integer_weight : (n : ℤ) - m = (j : ℤ) := by
      have hc : (((n : ℤ) - m : ℤ) : ℂ) = ((j : ℤ) : ℂ) := by
        simpa only [Int.cast_sub, Int.cast_natCast] using hjweight
      exact_mod_cast hc
    have lower := minimal j ⟨mode D a s m v, stable m v hvW, hjG, hnz⟩
    omega
  have nzero : n = 0 := by
    have roots := NormFourHighestWeight.highest_weight_values D a ha s hs
      (n : ℂ) v hvnz veigen positive
    have natural_gap : (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
      by_cases hz : n = 0
      · left; simp [hz]
      · right; exact_mod_cast (show 1 ≤ n by omega)
    rcases roots with zero | sixteenth | half
    · exact_mod_cast zero
    · have re := congrArg Complex.re sixteenth
      norm_num at re
      rcases natural_gap with hz | hpos <;> linarith
    · have re := congrArg Complex.re half
      norm_num at re
      rcases natural_gap with hz | hpos <;> linarith
  have hvline : v ∈ Submodule.span ℂ {vacuum D} := by
    rw [← grade_zero D a s]
    change v ∈ gradeSpace D a s n at hvG
    simpa only [nzero] using hvG
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvline
  have cnz : c ≠ 0 := by
    have nz : c • vacuum D ≠ 0 := by rw [hc]; exact hvnz
    exact (smul_ne_zero_iff.mp nz).1
  have vacuumW : vacuum D ∈ W := by
    have recovered := W.smul_mem c⁻¹ hvW
    rw [← hc, smul_smul, inv_mul_cancel₀ cnz, one_smul] at recovered
    exact recovered
  have cyclic : vacuumDescendants D a s ≤ W := by
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    induction w with
    | nil => exact vacuumW
    | cons k w ih => exact stable (-((k : ℤ) + 1)) _ ih
  apply top_unique
  intro x _
  obtain ⟨y, hy, heq⟩ := cyclic x.property
  have yx : y = x := Subtype.ext heq
  exact yx ▸ hy

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
