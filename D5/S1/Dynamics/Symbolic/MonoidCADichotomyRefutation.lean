/- GID: D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim; result=D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.result; claim=D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim
   digest: A Boolean OR automaton refutes the finite-monoid entropy dichotomy. -/

import D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
import Mathlib.Topology.UniformSpace.Equicontinuity

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.MonoidCADichotomyRefutation

open _root_.Dynamics Filter Function Set
open LatticeGardenOfEden (localMap)
open SymbolicDynamics.FullShift (shift shift_apply)
open scoped Topology Uniformity SetRel

private abbrev Lattice (D : ℕ) := Fin D → ℤ

private def windowRel {I A : Type*} (W : Finset I) : SetRel (I → A) (I → A) :=
  {p | ∀ z ∈ W, p.1 z = p.2 z}

private theorem window_basis (I A : Type*) [UniformSpace A] [DiscreteUniformity A] :
    (𝓤 (I → A)).HasBasis (fun _ : Finset I => True) (windowRel (A := A)) := by
  classical
  rw [Pi.uniformity]
  simp_rw [DiscreteUniformity.eq_principal_setRelId, Filter.comap_principal]
  refine (Filter.hasBasis_iInf_principal_finite
    (fun i : I => (fun p : (I → A) × (I → A) => (p.1 i, p.2 i)) ⁻¹' SetRel.id)).to_hasBasis ?_ ?_
  · intro S hS
    refine ⟨hS.toFinset, trivial, ?_⟩
    intro p hp
    simpa [windowRel, SetRel.id] using hp
  · intro W _
    refine ⟨W, W.finite_toSet, ?_⟩
    intro p hp
    simpa [windowRel, SetRel.id] using hp

private def box (D r : ℕ) : Finset (Lattice D) :=
  Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) (r : ℤ)

private theorem mem_box {D r : ℕ} {z : Lattice D} :
    z ∈ box D r ↔ ∀ i, -(r : ℤ) ≤ z i ∧ z i ≤ (r : ℤ) := by
  simp [box, Fintype.mem_piFinset]

private theorem window_subset_box {D : ℕ} (W : Finset (Lattice D)) :
    ∃ r, W ⊆ box D r := by
  let radius (z : Lattice D) := Finset.univ.sup fun i => (z i).natAbs
  refine ⟨W.sup radius, fun z hz => mem_box.mpr fun i => ?_⟩
  have hi : (z i).natAbs ≤ radius z := Finset.le_sup
    (f := fun j : Fin D => (z j).natAbs) (Finset.mem_univ i)
  have hz' : radius z ≤ W.sup radius := Finset.le_sup hz
  have h := hi.trans hz'
  omega

private theorem box_basis (D : ℕ) (A : Type*) [UniformSpace A] [DiscreteUniformity A] :
    (𝓤 (Lattice D → A)).HasBasis (fun _ : ℕ => True) (fun r => windowRel (A := A) (box D r)) := by
  refine (window_basis (Lattice D) A).to_hasBasis ?_ ?_
  · intro W _
    obtain ⟨r, hr⟩ := window_subset_box W
    exact ⟨r, trivial, fun _ hp z hz => hp z (hr hz)⟩
  · exact fun r _ => ⟨box D r, trivial, Subset.rfl⟩

private def sourceDist {D : ℕ} {A : Type*} (x y : Lattice D → A) : ℝ :=
  open Classical in
  if h : ∃ r, (x, y) ∉ windowRel (box D r) then (1 / 2 : ℝ) ^ Nat.find h else 0

private theorem sourceDist_lt_iff {D : ℕ} {A : Type*} (x y : Lattice D → A) (r : ℕ) :
    sourceDist x y < (1 / 2 : ℝ) ^ r ↔ (x, y) ∈ windowRel (box D r) := by
  classical
  unfold sourceDist
  split_ifs with h
  · rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)]
    constructor
    · exact fun hr => not_not.mp (Nat.find_min h hr)
    · intro hr
      by_contra! hmin
      apply Nat.find_spec h
      intro z hz
      apply hr z (mem_box.mpr fun i => ?_)
      have hzi := mem_box.mp hz i
      have hcast : (Nat.find h : ℤ) ≤ (r : ℤ) := by exact_mod_cast hmin
      omega
  · exact iff_of_true (by positivity) (by exact not_exists.mp h r |> not_not.mp)

private theorem sourceDist_basis (D : ℕ) (A : Type*) [UniformSpace A] [DiscreteUniformity A] :
    (𝓤 (Lattice D → A)).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {p | sourceDist p.1 p.2 < ε}) := by
  refine (box_basis D A).to_hasBasis ?_ ?_
  · intro r _
    exact ⟨(1 / 2 : ℝ) ^ r, by positivity, fun p hp => (sourceDist_lt_iff p.1 p.2 r).mp hp⟩
  · intro ε hε
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨r, trivial, fun p hp => ((sourceDist_lt_iff p.1 p.2 r).mpr hp).trans hr⟩

private def sensitive {X : Type*} [UniformSpace X] (F : X → X) : Prop :=
  ∃ U ∈ 𝓤 X, ∀ x, ∀ V ∈ 𝓤 X, ∃ y k, (x, y) ∈ V ∧ (F^[k] x, F^[k] y) ∉ U

private theorem sensitive_iff_basis {X I : Type*} [UniformSpace X] {F : X → X}
    {p : I → Prop} {s : I → SetRel X X} (basis : (𝓤 X).HasBasis p s) :
    sensitive F ↔ ∃ i, p i ∧ ∀ x j, p j → ∃ y k, (x, y) ∈ s j ∧ (F^[k] x, F^[k] y) ∉ s i := by
  constructor
  · rintro ⟨U, hU, h⟩
    obtain ⟨i, hi, hiU⟩ := basis.mem_iff.mp hU
    refine ⟨i, hi, fun x j hj => ?_⟩
    obtain ⟨y, k, hxy, hsep⟩ := h x (s j) (basis.mem_of_mem hj)
    exact ⟨y, k, hxy, fun hmem => hsep (hiU hmem)⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨s i, basis.mem_of_mem hi, fun x V hV => ?_⟩
    obtain ⟨j, hj, hjV⟩ := basis.mem_iff.mp hV
    obtain ⟨y, k, hxy, hsep⟩ := h x j hj
    exact ⟨y, k, hjV hxy, hsep⟩

private theorem source_equicontinuous_iff {D : ℕ} {A : Type*} [UniformSpace A] [DiscreteUniformity A]
    (F : (Lattice D → A) → (Lattice D → A)) :
    UniformEquicontinuous (fun k : ℕ => F^[k]) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y, sourceDist x y < δ →
        ∀ k : ℕ, sourceDist (F^[k] x) (F^[k] y) < ε :=
  (sourceDist_basis D A).uniformEquicontinuous_iff (sourceDist_basis D A)

private theorem source_sensitive_iff {D : ℕ} {A : Type*} [UniformSpace A] [DiscreteUniformity A]
    (F : (Lattice D → A) → (Lattice D → A)) :
    sensitive F ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ (x : Lattice D → A) (δ : ℝ), 0 < δ →
      ∃ (y : Lattice D → A) (k : ℕ), sourceDist x y < δ ∧ ε ≤ sourceDist (F^[k] x) (F^[k] y) := by
  simpa only [mem_ofPred_eq, not_lt] using sensitive_iff_basis (F := F) (sourceDist_basis D A)

/-- The finite-monoid extension of the entropy-bearing dichotomy in
Castronuovo–Dennunzio–Kari–Margara, Theorem 6 and §9. The finite local
presentation and the global unital monoid endomorphism act on the full shift. -/
def claim : Prop :=
  ∀ (D : ℕ), 2 ≤ D → ∀ (A : Type) [Fintype A] [Monoid A],
    letI : UniformSpace A := ⊥
    ∀ F : (Lattice D → A) →* (Lattice D → A),
      (∃ (W : Finset (Lattice D)) (rule : (W → A) → A), (F : _ → _) = localMap W rule) →
      (UniformEquicontinuous (fun k : ℕ => (F : _ → _)^[k]) ∧ coverEntropy F univ = 0) ∨
      (sensitive F ∧ coverEntropy F univ = ⊤)

private theorem localMap_continuous {D : ℕ} {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (W : Finset (Lattice D)) (rule : (W → A) → A) :
    Continuous (localMap W rule) := by
  apply continuous_pi
  intro z
  exact (continuous_of_discreteTopology : Continuous rule).comp
    (continuous_pi fun s : W => continuous_apply (z + s.val))

private theorem localMap_shift {D : ℕ} {A : Type*} (W : Finset (Lattice D)) (rule : (W → A) → A)
    (u : Lattice D) (x : Lattice D → A) :
    localMap W rule (shift u x) = shift u (localMap W rule x) := by
  funext z
  simp only [shift_apply, localMap, add_assoc]

private local instance orMonoid : Monoid Bool where
  one := false
  mul := (· || ·)
  one_mul := Bool.false_or
  mul_one := Bool.or_false
  mul_assoc := Bool.or_assoc

private abbrev Config := Lattice 2 → Bool

private def east : Lattice 2 := Pi.single 0 1
private def north : Lattice 2 := Pi.single 1 1
private def offsets : Finset (Lattice 2) := {0, east, north}

private def orRule (p : offsets → Bool) : Bool :=
  p ⟨0, by simp [offsets]⟩ || p ⟨east, by simp [offsets]⟩ || p ⟨north, by simp [offsets]⟩

private theorem local_or_apply (x : Config) (z : Lattice 2) :
    localMap offsets orRule x z = (x z || x (z + east) || x (z + north)) := by
  simp [localMap, orRule]

private def orCA : Config →* Config where
  toFun := localMap offsets orRule
  map_one' := by
    ext z
    rw [local_or_apply]
    rfl
  map_mul' x y := by
    ext z
    change localMap offsets orRule (x * y) z =
      (localMap offsets orRule x * localMap offsets orRule y) z
    simp only [Pi.mul_apply, local_or_apply]
    change
      ((x z || y z) || (x (z + east) || y (z + east)) || (x (z + north) || y (z + north))) =
      ((x z || x (z + east) || x (z + north)) || (y z || y (z + east) || y (z + north)))
    ac_rfl

private theorem or_apply (x : Config) (z : Lattice 2) :
    orCA x z = (x z || x (z + east) || x (z + north)) :=
  local_or_apply x z

private def seed (u : Lattice 2) : Config := fun z => decide (z = u)

private theorem axes_essential :
    ∀ u ∈ ({east, north} : Finset (Lattice 2)),
      ∃ x y : Config, (∀ z, z ≠ u → x z = y z) ∧ orCA x 0 ≠ orCA y 0 := by
  intro u hu
  refine ⟨fun _ => false, seed u, fun z hz => by simp [seed, hz], ?_⟩
  rcases Finset.mem_insert.mp hu with rfl | hu
  · simp [or_apply, seed]
  · have hu' : u = north := Finset.mem_singleton.mp hu
    subst u
    simp [or_apply, seed]

private theorem or_iterate_constant (b : Bool) (k : ℕ) :
    (orCA : Config → Config)^[k] (fun _ => b) = fun _ => b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih]
    funext z
    cases b <;> rfl

private theorem or_step (x : Config) (z : Lattice 2) :
    x z ≤ orCA x z := by
  rw [or_apply]
  cases x z <;> simp

private theorem or_iterate_mono (x : Config) (z : Lattice 2) :
    Monotone fun k : ℕ => (orCA : Config → Config)^[k] x z := by
  apply monotone_nat_of_le_succ
  intro k
  rw [iterate_succ_apply']
  exact or_step _ z

private theorem east_propagates (x : Config) (k : ℕ) (z : Lattice 2)
    (h : x (z + k • east) = true) :
    (orCA : Config → Config)^[k] x z = true := by
  induction k generalizing z with
  | zero => simpa using h
  | succ k ih =>
    rw [iterate_succ_apply', or_apply]
    have h' : x ((z + east) + k • east) = true := by
      simpa only [succ_nsmul, add_assoc, add_left_comm, add_comm] using h
    simp [ih (z + east) h']

private theorem or_not_equicontinuous :
    ¬ UniformEquicontinuous (fun k : ℕ => (orCA : Config → Config)^[k]) := by
  rw [(box_basis 2 Bool).uniformEquicontinuous_iff (box_basis 2 Bool)]
  intro h
  obtain ⟨r, _, hr⟩ := h 0 trivial
  let u : Lattice 2 := (r + 1) • east
  have hu : u ∉ box 2 r := by
    intro hmem
    have hbound := (mem_box.mp hmem (0 : Fin 2)).2
    simp [u, east, nsmul_eq_mul] at hbound
  have hagree : ((fun _ : Lattice 2 => false), seed u) ∈ windowRel (box 2 r) := by
    intro z hz
    have hzu : z ≠ u := fun h => hu (h ▸ hz)
    simp [seed, hzu]
  have hzero : (0 : Lattice 2) ∈ box 2 0 := by simp [mem_box]
  have hbad := hr _ _ hagree (r + 1) 0 hzero
  change (orCA : Config → Config)^[r + 1] (fun _ => false) 0 =
    (orCA : Config → Config)^[r + 1] (seed u) 0 at hbad
  rw [or_iterate_constant, east_propagates (seed u) (r + 1) 0 (by simp [u, seed])] at hbad
  exact Bool.false_ne_true hbad

private theorem or_not_sensitive : ¬ sensitive (orCA : Config → Config) := by
  rw [sensitive_iff_basis (box_basis 2 Bool)]
  rintro ⟨r, _, h⟩
  obtain ⟨y, k, hxy, hbad⟩ := h (fun _ => true) r trivial
  apply hbad
  intro z hz
  have hstart : y z = true := (hxy z hz).symm
  have hp := or_iterate_mono y z (Nat.zero_le k)
  change y z ≤ (orCA : Config → Config)^[k] y z at hp
  rw [hstart] at hp
  change (orCA : Config → Config)^[k] (fun _ => true) z = (orCA : Config → Config)^[k] y z
  rw [or_iterate_constant]
  exact le_antisymm hp (by simp)

/-- The remote seed and the persistent all-true window exclude the two alternatives. -/
theorem result : ¬ claim := by
  intro h
  rcases h 2 (by decide) Bool orCA ⟨offsets, orRule, rfl⟩ with hl | hr
  · exact or_not_equicontinuous hl.1
  · exact or_not_sensitive hr.1

#print axioms localMap_continuous
#print axioms localMap_shift
#print axioms source_equicontinuous_iff
#print axioms source_sensitive_iff
#print axioms axes_essential
#print axioms or_not_equicontinuous
#print axioms or_not_sensitive
#print axioms result

end D5.S1.Dynamics.Symbolic.MonoidCADichotomyRefutation
