/- GID: D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim; result=D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.result; claim=D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim
   digest: A Boolean OR automaton refutes the finite-monoid entropy dichotomy. -/

import D5.S1.Dynamics.Symbolic.LatticeGardenOfEden

/-! The finite-monoid dichotomy fails on the two-dimensional Boolean OR full shift. -/

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.MonoidCADichotomyRefutation

open _root_.Dynamics ExpGrowth Filter Function Set
open LatticeGardenOfEden (localMap)
open SymbolicDynamics.FullShift (shift shift_apply)
open scoped ENNReal Topology Uniformity SetRel

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

/-- The source distance uses the least centered-box radius that sees a disagreement. -/
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
  · exact iff_of_true (by positivity) (not_not.mp (not_exists.mp h r))

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

private theorem source_equicontinuous_iff {D : ℕ} {A : Type*}
    [UniformSpace A] [DiscreteUniformity A]
    (F : (Lattice D → A) → (Lattice D → A)) :
    UniformEquicontinuous (fun k : ℕ => F^[k]) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y, sourceDist x y < δ →
        ∀ k : ℕ, sourceDist (F^[k] x) (F^[k] y) < ε :=
  (sourceDist_basis D A).uniformEquicontinuous_iff (sourceDist_basis D A)

/-- The finite-monoid extension of the entropy-bearing dichotomy in
Castronuovo–Dennunzio–Kari–Margara, Theorem 6 and §9. The finite local
presentation and the global unital monoid endomorphism act on the full shift. -/
def claim : Prop :=
  ∀ (D : ℕ), 2 ≤ D → ∀ (A : Type) [Fintype A] [Monoid A],
    letI : UniformSpace A := ⊥
    ∀ F : (Lattice D → A) →* (Lattice D → A),
      (∃ (W : Finset (Lattice D)) (rule : (W → A) → A), (F : _ → _) = localMap W rule) →
      Continuous (F : _ → _) →
      (∀ u x, F (shift u x) = shift u (F x)) →
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

private theorem or_persists (x : Config) (z : Lattice 2) {t k : ℕ} (htk : t ≤ k)
    (h : (orCA : Config → Config)^[t] x z = true) :
    (orCA : Config → Config)^[k] x z = true := by
  have hm := or_iterate_mono x z htk
  change (orCA : Config → Config)^[t] x z ≤ (orCA : Config → Config)^[k] x z at hm
  rw [h] at hm
  exact Bool.eq_true_of_true_le hm

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
  rw [source_equicontinuous_iff]
  intro h
  obtain ⟨δ, hδ, heq⟩ := h 1 zero_lt_one
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  let u : Lattice 2 := (r + 1) • east
  have hu : u ∉ box 2 r := by
    intro hmem
    have hbound := (mem_box.mp hmem (0 : Fin 2)).2
    simp [u, east, nsmul_eq_mul] at hbound
  have hagree : ((fun _ : Lattice 2 => false), seed u) ∈ windowRel (box 2 r) := by
    intro z hz
    have hzu : z ≠ u := fun h => hu (h ▸ hz)
    simp [seed, hzu]
  have hclose := heq _ _ (((sourceDist_lt_iff _ _ r).mpr hagree).trans hr) (r + 1)
  have hcloseZero : sourceDist ((orCA : Config → Config)^[r + 1] (fun _ => false))
      ((orCA : Config → Config)^[r + 1] (seed u)) < (1 / 2 : ℝ) ^ 0 := by
    simpa only [pow_zero] using hclose
  have hzero : (0 : Lattice 2) ∈ box 2 0 := by simp [mem_box]
  have hbad := (sourceDist_lt_iff _ _ 0).mp hcloseZero 0 hzero
  change (orCA : Config → Config)^[r + 1] (fun _ => false) 0 =
    (orCA : Config → Config)^[r + 1] (seed u) 0 at hbad
  rw [or_iterate_constant, east_propagates (seed u) (r + 1) 0 (by simp [u, seed])] at hbad
  exact Bool.false_ne_true hbad

private def trace {I A : Type*} (F : (I → A) → (I → A))
    (W : Finset I) (n : ℕ) (x : I → A) : Fin n × W → A :=
  fun p => F^[p.1.val] x p.2.val

private theorem trace_eq_iff {I A : Type*} (F : (I → A) → (I → A))
    (W : Finset I) (n : ℕ) (x y : I → A) :
    trace F W n x = trace F W n y ↔ (x, y) ∈ dynEntourage F (windowRel W) n := by
  rw [mem_dynEntourage]
  exact ⟨fun h k hk z hz => congrFun h (⟨k, hk⟩, ⟨z, hz⟩),
    fun h => funext fun p => h p.1.val p.1.isLt p.2.val p.2.property⟩

/-- Every realized trace supplies a center, and a center covers exactly one trace class. -/
private theorem coverMincard_eq_traceCount {I A : Type*} [Finite A] (F : (I → A) → (I → A))
    (W : Finset I) (n : ℕ) :
    coverMincard F univ (windowRel W) n = (Nat.card (range (trace F W n)) : ℕ∞) := by
  classical
  let T := range (trace F W n)
  let rep (t : T) : I → A := t.property.choose
  have hrep (t : T) : trace F W n (rep t) = t.val := t.property.choose_spec
  let : Fintype T := Fintype.ofFinite T
  apply le_antisymm
  · let centers : Finset (I → A) := Finset.univ.image rep
    have hc : IsDynCoverOf F univ (windowRel W) n centers := by
      intro x _
      let t : T := ⟨trace F W n x, mem_range_self x⟩
      exact ⟨rep t, Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩,
        (trace_eq_iff F W n _ _).mp (hrep t).symm⟩
    refine hc.coverMincard_le_card.trans ?_
    exact_mod_cast (show centers.card ≤ Nat.card T from
      Finset.card_image_le.trans_eq (by rw [Finset.card_univ, Nat.card_eq_fintype_card]))
  · unfold coverMincard
    refine le_iInf₂ fun centers hc => ?_
    have hcenter (t : T) : ∃ c : centers, trace F W n c.val = t.val := by
      obtain ⟨c, hmem, hclose⟩ := hc (x := rep t) (mem_univ _)
      exact ⟨⟨c, hmem⟩, ((trace_eq_iff F W n _ _).mpr hclose).symm.trans (hrep t)⟩
    choose center hcenter using hcenter
    have hinj : Injective center := by
      intro t u h
      apply Subtype.ext
      rw [← hcenter t, ← hcenter u, h]
    have hcard := Nat.card_le_card_of_injective center hinj
    have hcCard : Nat.card ↥centers = centers.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact_mod_cast hcard.trans_eq hcCard

private theorem exists_cutoff (x : Config) (z : Lattice 2) (n : ℕ) :
    ∃ t, n ≤ t ∨ (orCA : Config → Config)^[t] x z = true :=
  ⟨n, Or.inl le_rfl⟩

/-- The first time a coordinate is true, with `n` encoding an all-false trace. -/
private def cutoff (x : Config) (z : Lattice 2) (n : ℕ) : Fin (n + 1) :=
  open Classical in
  ⟨Nat.find (exists_cutoff x z n),
    Nat.lt_succ_of_le (Nat.find_min' (exists_cutoff x z n) (Or.inl le_rfl))⟩

private theorem cutoff_spec (x : Config) (z : Lattice 2) {n : ℕ} (k : Fin n) :
    (orCA : Config → Config)^[k.val] x z = true ↔ (cutoff x z n).val ≤ k.val := by
  classical
  change _ ↔ Nat.find (exists_cutoff x z n) ≤ k.val
  refine ⟨fun h => Nat.find_min' (exists_cutoff x z n) (Or.inr h), fun hk => ?_⟩
  have ht := (Nat.find_spec (exists_cutoff x z n)).resolve_left
    (not_le_of_gt (hk.trans_lt k.isLt))
  exact or_persists x z hk ht

private theorem or_traceCount_le (W : Finset (Lattice 2)) (n : ℕ) :
    Nat.card (range (trace (orCA : Config → Config) W n)) ≤ (n + 1) ^ W.card := by
  classical
  let T := range (trace (orCA : Config → Config) W n)
  let code (t : T) (z : W) : Fin (n + 1) := cutoff t.property.choose z.val n
  have hinj : Injective code := by
    intro t u h
    apply Subtype.ext
    rw [← t.property.choose_spec, ← u.property.choose_spec]
    funext p
    have hp := congrArg Fin.val (congrFun h p.2)
    change (cutoff t.property.choose p.2.val n).val =
      (cutoff u.property.choose p.2.val n).val at hp
    apply Bool.eq_iff_iff.mpr
    change (orCA : Config → Config)^[p.1.val] t.property.choose p.2.val = true ↔
      (orCA : Config → Config)^[p.1.val] u.property.choose p.2.val = true
    rw [cutoff_spec, cutoff_spec, hp]
  calc
    _ ≤ Nat.card (W → Fin (n + 1)) := Nat.card_le_card_of_injective code hinj
    _ = (n + 1) ^ W.card := by simp [Nat.card_eq_fintype_card]

private theorem polynomial_growth_zero (m : ℕ) :
    expGrowthSup (fun n : ℕ => (((n + 1) ^ m : ℕ) : ℝ≥0∞)) = 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp htop using 1
    funext n
    simp
  have hlim : Tendsto (fun n : ℕ => Real.log (((n + 1) ^ m : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow, mul_div_assoc, mul_zero]
      using hlog.const_mul (m : ℝ)
  apply Tendsto.limsup_eq
  refine (EReal.tendsto_coe.mpr hlim).congr (fun n => ?_)
  change ((Real.log (((n + 1) ^ m : ℕ) : ℝ) / n : ℝ) : EReal) =
    ENNReal.log (↑((n + 1) ^ m : ℕ)) / (n : EReal)
  rw [ENNReal.log_pos_real (by positivity) (by simp), ENNReal.toReal_natCast, EReal.coe_div,
    EReal.coe_natCast]

private theorem or_entropy_zero : coverEntropy (orCA : Config → Config) univ = 0 := by
  apply le_antisymm _ (coverEntropy_nonneg _ univ_nonempty)
  rw [coverEntropy_eq_iSup_basis (box_basis 2 Bool)]
  refine iSup₂_le fun r _ => ?_
  unfold coverEntropyEntourage
  refine (expGrowthSup_monotone (b := fun n : ℕ => ↑((n + 1) ^ (box 2 r).card : ℕ))
    fun n => ?_).trans_eq (polynomial_growth_zero _)
  rw [coverMincard_eq_traceCount, ENat.toENNReal_coe]
  change (Nat.card (range (trace (orCA : Config → Config) (box 2 r) n)) : ℝ≥0∞) ≤
    (((n + 1) ^ (box 2 r).card : ℕ) : ℝ≥0∞)
  exact_mod_cast or_traceCount_le (box 2 r) n

/-- The propagating seed excludes the equicontinuous branch. Zero full-shift
entropy excludes the infinite-entropy branch. -/
theorem result : ¬ claim := by
  intro h
  rcases h 2 (by decide) Bool orCA ⟨offsets, orRule, rfl⟩
    (localMap_continuous offsets orRule) (localMap_shift offsets orRule) with hl | hr
  · exact or_not_equicontinuous hl.1
  · exact EReal.zero_ne_top (or_entropy_zero.symm.trans hr.2)

end D5.S1.Dynamics.Symbolic.MonoidCADichotomyRefutation
