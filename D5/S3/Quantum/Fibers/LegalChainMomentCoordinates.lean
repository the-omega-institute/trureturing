/- GID: D5/S3/Quantum/Fibers/LegalChainMomentCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/LegalChainMomentCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral inversion and actual polar forms on positive legal-chain fibres. -/

import Mathlib

/-! Legal path moments, actual phase period quotients and their polar source forms. -/

noncomputable section

namespace D5.S3.Quantum.Fibers.LegalChainMomentCoordinates

open Finset Matrix
open scoped BigOperators

/-- A subset of the path has no pair of consecutive occupied positions. -/
def Legal {n : ℕ} (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i.val + 1 ≠ j.val

/-- The actual independent subsets of the path, including the empty subset. -/
abbrev Pattern (n : ℕ) := {I : Finset (Fin n) // Legal I}

instance (n : ℕ) : Fintype (Pattern n) := Fintype.ofFinite _
instance (n : ℕ) : DecidableEq (Pattern n) := Classical.decEq _

private theorem legal_subset {n : ℕ} {I J : Finset (Fin n)}
    (h : I ⊆ J) (hJ : Legal J) : Legal I := by
  intro i hi j hj
  exact hJ i (h hi) j (h hj)

/-- The empty pattern. -/
def emptyPattern (n : ℕ) : Pattern n := ⟨∅, by simp [Legal]⟩

/-- The upper incidence matrix, over the actual integral lattice of legal patterns. -/
def incidence (n : ℕ) : Matrix (Pattern n) (Pattern n) ℤ :=
  fun T I => if T.val ⊆ I.val then 1 else 0

/-- The signed upper incidence matrix. -/
def signedIncidence (n : ℕ) : Matrix (Pattern n) (Pattern n) ℤ :=
  fun I T => if I.val ⊆ T.val then (-1) ^ (T.val.card - I.val.card) else 0

private theorem interval_cancellation {n : ℕ} (I J : Pattern n) (hIJ : I.val ⊆ J.val) :
    (∑ T : Pattern n, if I.val ⊆ T.val ∧ T.val ⊆ J.val then
      (-1 : ℤ) ^ (T.val.card - I.val.card) else 0) = if I = J then 1 else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hsum :
      (∑ T ∈ Finset.univ.filter (fun T : Pattern n => I.val ⊆ T.val ∧ T.val ⊆ J.val),
        (-1 : ℤ) ^ (T.val.card - I.val.card)) =
      ∑ U ∈ (J.val \ I.val).powerset, (-1 : ℤ) ^ U.card := by
    refine Finset.sum_bij (fun T _ => T.val \ I.val) ?_ ?_ ?_ ?_
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      apply Finset.mem_powerset.mpr
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hT.2 (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    · intro T hT V hV heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hV
      apply Subtype.ext
      calc
        T.val = I.val ∪ (T.val \ I.val) := (Finset.union_sdiff_of_subset hT.1).symm
        _ = I.val ∪ (V.val \ I.val) := by rw [heq]
        _ = V.val := Finset.union_sdiff_of_subset hV.1
    · intro U hU
      have hU' := Finset.mem_powerset.mp hU
      have hsub : I.val ∪ U ⊆ J.val := Finset.union_subset hIJ
        (hU'.trans Finset.sdiff_subset)
      refine ⟨⟨I.val ∪ U, legal_subset hsub J.property⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Finset.subset_union_left, hsub⟩
      · dsimp
        rw [Finset.union_sdiff_left]
        exact Finset.sdiff_eq_self_iff_disjoint.mpr (Finset.disjoint_of_subset_left hU'
          Finset.sdiff_disjoint)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rw [Finset.card_sdiff_of_subset hT.1]
  rw [hsum, Finset.sum_powerset_neg_one_pow_card]
  congr 1
  apply propext
  constructor
  · intro h
    apply Subtype.ext
    exact le_antisymm hIJ (Finset.sdiff_eq_empty_iff_subset.mp h)
  · intro h
    simp [h]

/-- Möbius cancellation holds in the actual integral pattern lattice. -/
private theorem signed_mul_incidence (n : ℕ) : signedIncidence n * incidence n = 1 := by
  classical
  ext I J
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ T : Pattern n,
      signedIncidence n I T * incidence n T J =
      if I.val ⊆ T.val ∧ T.val ⊆ J.val then
        (-1 : ℤ) ^ (T.val.card - I.val.card) else 0 := by
    intro T
    simp only [signedIncidence, incidence]
    split_ifs <;> simp_all
  simp_rw [hterm]
  by_cases hIJ : I.val ⊆ J.val
  · exact interval_cancellation I J hIJ
  · have hne : I ≠ J := by intro h; exact hIJ (h ▸ Finset.Subset.refl _)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro T _
    exact if_neg (fun h => hIJ (h.1.trans h.2))

/-- The reverse product is also the identity over the integers. -/
private theorem incidence_mul_signed (n : ℕ) : incidence n * signedIncidence n = 1 :=
  (mul_eq_one_comm).mp (signed_mul_incidence n)

/-- Integer matrices act on every additive commutative group, including a phase circle. -/
def act {ι : Type*} [Fintype ι] {G : Type*} [AddCommGroup G]
    (A : Matrix ι ι ℤ) (x : ι → G) : ι → G :=
  fun i => ∑ j, A i j • x j

private theorem act_mul {ι : Type*} [Fintype ι] {G : Type*} [AddCommGroup G]
    (A B : Matrix ι ι ℤ) (x : ι → G) : act (A * B) x = act A (act B x) := by
  classical
  funext i
  simp only [act, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

private theorem act_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [AddCommGroup G] (x : ι → G) : act (1 : Matrix ι ι ℤ) x = x := by
  ext i
  simp [act, Matrix.one_apply]

/-- Upper sums of a function on legal patterns. For probabilities these are occupation moments. -/
def moments {n : ℕ} {G : Type*} [AddCommGroup G] (p : Pattern n → G) : Pattern n → G :=
  act (incidence n) p

/-- Signed upper sums reconstruct the original function from its moments. -/
def probabilities {n : ℕ} {G : Type*} [AddCommGroup G]
    (mu : Pattern n → G) : Pattern n → G := act (signedIncidence n) mu

/-- Signed lower sums give the relation phases; the definition is valid modulo any period. -/
def phases {n : ℕ} {G : Type*} [AddCommGroup G]
    (theta : Pattern n → G) : Pattern n → G := act (signedIncidence n).transpose theta

/-- Unsigned lower sums reconstruct each original phase. -/
def originalPhases {n : ℕ} {G : Type*} [AddCommGroup G]
    (phi : Pattern n → G) : Pattern n → G := act (incidence n).transpose phi

private theorem probabilities_moments {n : ℕ} {G : Type*} [AddCommGroup G]
    (p : Pattern n → G) : probabilities (moments p) = p := by
  rw [probabilities, moments, ← act_mul, signed_mul_incidence, act_one]

private theorem moments_probabilities {n : ℕ} {G : Type*} [AddCommGroup G]
    (mu : Pattern n → G) : moments (probabilities mu) = mu := by
  rw [moments, probabilities, ← act_mul, incidence_mul_signed, act_one]

private theorem original_phases_phases {n : ℕ} {G : Type*} [AddCommGroup G]
    (theta : Pattern n → G) : originalPhases (phases theta) = theta := by
  rw [originalPhases, phases, ← act_mul, ← Matrix.transpose_mul,
    signed_mul_incidence, Matrix.transpose_one, act_one]

private theorem phases_original_phases {n : ℕ} {G : Type*} [AddCommGroup G]
    (phi : Pattern n → G) : phases (originalPhases phi) = phi := by
  rw [phases, originalPhases, ← act_mul, ← Matrix.transpose_mul,
    incidence_mul_signed, Matrix.transpose_one, act_one]

/-- The moment transform is an additive equivalence on the full pattern lattice. -/
def momentEquiv (n : ℕ) (G : Type*) [AddCommGroup G] :
    (Pattern n → G) ≃+ (Pattern n → G) where
  toFun := moments
  invFun := probabilities
  left_inv := probabilities_moments
  right_inv := moments_probabilities
  map_add' := by intro x y; ext i; simp [moments, act, smul_add, Finset.sum_add_distrib]

/-- The phase transform is an additive equivalence even on the actual phase torus. -/
def phaseEquiv (n : ℕ) (G : Type*) [AddCommGroup G] :
    (Pattern n → G) ≃+ (Pattern n → G) where
  toFun := phases
  invFun := originalPhases
  left_inv := original_phases_phases
  right_inv := phases_original_phases
  map_add' := by intro x y; ext i; simp [phases, act, smul_add, Finset.sum_add_distrib]

/-- Real moments give a continuous linear change of coordinates. -/
def momentLinearEquiv (n : ℕ) : (Pattern n → ℝ) ≃ₗ[ℝ] (Pattern n → ℝ) :=
  { momentEquiv n ℝ with
    map_smul' := by
      intro c x
      funext i
      change moments (c • x) i = c • moments x i
      simp [moments, act, zsmul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm] }

/-- Real phase lifts have the dual continuous linear change of coordinates. -/
def phaseLinearEquiv (n : ℕ) : (Pattern n → ℝ) ≃ₗ[ℝ] (Pattern n → ℝ) :=
  { phaseEquiv n ℝ with
    map_smul' := by
      intro c x
      funext i
      change phases (c • x) i = c • phases x i
      simp [phases, act, zsmul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm] }

end D5.S3.Quantum.Fibers.LegalChainMomentCoordinates

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentQuotient

open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open scoped BigOperators

/-- Low order includes the empty pattern, whose action is common phase. -/
abbrev Low (n q : ℕ) := {T : Pattern n // T.val.card ≤ q}

/-- The surviving indices are precisely the legal subsets of order greater than q. -/
abbrev High (n q : ℕ) := {T : Pattern n // q < T.val.card}

instance (n q : ℕ) : Fintype (Low n q) := Fintype.ofFinite _
instance (n q : ℕ) : Fintype (High n q) := Fintype.ofFinite _

/-- Extend low coordinates by zero on all high patterns. -/
def lowEmbedding (n q : ℕ) (G : Type*) [AddCommGroup G] :
    (Low n q → G) →+ (Pattern n → G) where
  toFun t I := if h : I.val.card ≤ q then t ⟨I, h⟩ else 0
  map_zero' := by ext I; dsimp; split_ifs <;> rfl
  map_add' := by intro x y; ext I; dsimp; split_ifs <;> simp

/-- Extend high coordinates by zero on all low patterns. -/
def highEmbedding (n q : ℕ) (G : Type*) [AddCommGroup G] :
    (High n q → G) →+ (Pattern n → G) where
  toFun t I := if h : q < I.val.card then t ⟨I, h⟩ else 0
  map_zero' := by ext I; dsimp; split_ifs <;> rfl
  map_add' := by intro x y; ext I; dsimp; split_ifs <;> simp

/-- Occupation-moment phase rotations, including the common phase at the empty pattern. -/
def actionHom (n q : ℕ) (G : Type*) [AddCommGroup G] :
    (Low n q → G) →+ (Pattern n → G) :=
  (phaseEquiv n G).symm.toAddMonoidHom.comp (lowEmbedding n q G)

/-- The literal occupation phase rotations supplied by the fixed-moment menu. -/
def occupationAction (n q : ℕ) (G : Type*) [AddCommGroup G] :
    (Low n q → G) →+ (Pattern n → G) where
  toFun t I := ∑ T : Low n q, if T.val.val ⊆ I.val then t T else 0
  map_zero' := by ext I; simp
  map_add' := by
    intro t u
    ext I
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp

/-- The occupation generators are exactly the inverse-transform images of the low phase slots. -/
private theorem occupation_action_eq (n q : ℕ) (G : Type*) [AddCommGroup G] (t : Low n q → G) :
    occupationAction n q G t = actionHom n q G t := by
  classical
  ext I
  change (∑ T : Low n q, if T.val.val ⊆ I.val then t T else 0) =
    originalPhases (lowEmbedding n q G t) I
  simp only [originalPhases, act, Matrix.transpose_apply, incidence, ite_smul,
    one_smul, zero_smul]
  have h := Finset.sum_subtype (p := fun T : Pattern n => T.val.card ≤ q)
    (F := inferInstanceAs (Fintype (Low n q)))
    (Finset.univ.filter (fun T : Pattern n => T.val.card ≤ q))
    (by simp) (fun T : Pattern n => if T.val ⊆ I.val then lowEmbedding n q G t T else 0)
  calc
    _ = ∑ T : Low n q, if T.val.val ⊆ I.val then lowEmbedding n q G t T.val else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      simp [lowEmbedding, T.property]
    _ = _ := by
      rw [← h]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro T _ hT
      have ht : ¬ T.val.card ≤ q := by simpa using hT
      simp [lowEmbedding, ht]

/-- Two phase tuples belong to one orbit of the supplied low-moment phase actions. -/
def PhaseOrbit (n q : ℕ) (G : Type*) [AddCommGroup G]
    (theta eta : Pattern n → G) : Prop :=
  ∃ t : Low n q → G, eta = theta + occupationAction n q G t

/-- The actual orbit relation, independent of any proposed quotient coordinates. -/
def phaseSetoid (n q : ℕ) (G : Type*) [AddCommGroup G] :
    Setoid (Pattern n → G) where
  r := PhaseOrbit n q G
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro theta; exact ⟨0, by simp⟩
    · rintro theta eta ⟨t, rfl⟩
      exact ⟨-t, by simp⟩
    · rintro theta eta zeta ⟨t, rfl⟩ ⟨u, rfl⟩
      exact ⟨t + u, by simp [add_assoc]⟩

/-- High relation phases read from an actual original phase tuple. -/
def highPhases {n q : ℕ} {G : Type*} [AddCommGroup G]
    (theta : Pattern n → G) : High n q → G := fun T => phases theta T.val

/-- The high phases classify the actual low-moment orbits, with no residual finite kernel. -/
private theorem orbit_iff_high_phases {n q : ℕ} {G : Type*} [AddCommGroup G]
    (theta eta : Pattern n → G) :
    PhaseOrbit n q G theta eta ↔ highPhases (q := q) theta = highPhases eta := by
  classical
  change (∃ t, eta = theta + occupationAction n q G t) ↔ _
  simp_rw [occupation_action_eq]
  constructor
  · rintro ⟨t, rfl⟩
    funext T
    change phaseEquiv n G theta T.val =
      phaseEquiv n G (theta + (phaseEquiv n G).symm (lowEmbedding n q G t)) T.val
    rw [map_add, AddEquiv.apply_symm_apply]
    simp [lowEmbedding, not_le.mpr T.property]
  · intro h
    refine ⟨(fun T => phases eta T.val - phases theta T.val), ?_⟩
    apply (phaseEquiv n G).injective
    change phaseEquiv n G eta = phaseEquiv n G
      (theta + (phaseEquiv n G).symm (lowEmbedding n q G _))
    rw [map_add, AddEquiv.apply_symm_apply]
    funext I
    by_cases hI : I.val.card ≤ q
    · change phases eta I = phases theta I + _
      simp [lowEmbedding, hI]
    · have hi := congrFun h (⟨I, not_le.mp hI⟩ : High n q)
      change phases theta I = phases eta I at hi
      change phases eta I = phases theta I + _
      simp [lowEmbedding, hI, hi]

/-- Strict probabilities on the actual legal-pattern simplex. -/
abbrev PositiveProbability (n : ℕ) :=
  {p : Pattern n → ℝ // (∀ I, 0 < p I) ∧ ∑ I, p I = 1}

/-- The fixed-moment fibre uses an arbitrary positive reference in that fibre. -/
abbrev ProbabilityFibre {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :=
  {p : PositiveProbability n // ∀ T : Low n q, moments p.val T.val = moments p0.val T.val}

/-- Fill the low slots with their prescribed values and the high slots with x. -/
def fillMoments {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x : High n q → ℝ) : Pattern n → ℝ :=
  fun I => if h : I.val.card ≤ q then moments p0.val I else x ⟨I, not_le.mp h⟩

/-- The domain is cut out by the actual inverse probabilities being strictly positive. -/
def positiveDomain {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Set (High n q → ℝ) :=
  {x | ∀ I, 0 < probabilities (fillMoments q p0 x) I}

private theorem moment_empty {n : ℕ} (p : Pattern n → ℝ) :
    moments p (emptyPattern n) = ∑ I, p I := by
  simp [moments, act, incidence, emptyPattern]

private theorem filled_normalized {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x : High n q → ℝ) : ∑ I, probabilities (fillMoments q p0 x) I = 1 := by
  rw [← moment_empty]
  have he : moments (probabilities (fillMoments q p0 x)) = fillMoments q p0 x :=
    (momentEquiv n ℝ).apply_symm_apply _
  rw [he]
  have hzero : (emptyPattern n).val.card ≤ q := by simp [emptyPattern]
  simp only [fillMoments, dif_pos hzero]
  rw [moment_empty]
  exact p0.property.2

private theorem fill_from_fibre {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (p : ProbabilityFibre q p0) :
    fillMoments q p0 (fun T => moments p.val.val T.val) = moments p.val.val := by
  funext I
  dsimp [fillMoments]
  split_ifs with h
  · exact (p.property ⟨I, h⟩).symm
  · rfl

/-- All and only the high moments vary on each positive fixed-moment fibre. -/
def probabilityFibreEquiv {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    ProbabilityFibre q p0 ≃ positiveDomain q p0 where
  toFun p := ⟨fun T => moments p.val.val T.val, by
    change ∀ I, 0 < probabilities (fillMoments q p0 _) I
    rw [fill_from_fibre]
    have he : probabilities (moments p.val.val) = p.val.val :=
      (momentEquiv n ℝ).symm_apply_apply _
    rw [he]
    exact p.val.property.1⟩
  invFun x := ⟨⟨probabilities (fillMoments q p0 x.val),
    x.property, filled_normalized q p0 x.val⟩, by
      intro T
      have he : moments (probabilities (fillMoments q p0 x.val)) = fillMoments q p0 x.val :=
        (momentEquiv n ℝ).apply_symm_apply _
      rw [he]
      simp [fillMoments, T.property]⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change probabilities (fillMoments q p0 _) = p.val.val
    rw [fill_from_fibre]
    exact (momentEquiv n ℝ).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    funext T
    change moments (probabilities (fillMoments q p0 x.val)) T.val = x.val T
    have he : moments (probabilities (fillMoments q p0 x.val)) = fillMoments q p0 x.val :=
      (momentEquiv n ℝ).apply_symm_apply _
    rw [he]
    simp [fillMoments, not_le.mpr T.property]

/-- Every positive reference supplies a point of the high-moment domain. -/
private theorem positive_domain_nonempty {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    (positiveDomain q p0).Nonempty := by
  exact ⟨_, (probabilityFibreEquiv q p0 ⟨p0, fun _ => rfl⟩).property⟩

private theorem continuous_fill {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Continuous (fillMoments q p0) := by
  classical
  apply continuous_pi
  intro I
  dsimp [fillMoments]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

private theorem continuous_probabilities (n : ℕ) :
    Continuous (probabilities : (Pattern n → ℝ) → Pattern n → ℝ) :=
  (momentLinearEquiv n).symm.toContinuousLinearEquiv.continuous

/-- The high-moment probability domain is open in the full high-coordinate space. -/
private theorem positive_domain_open {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    IsOpen (positiveDomain q p0) := by
  classical
  have hcont := (continuous_probabilities n).comp (continuous_fill q p0)
  change IsOpen {x | ∀ I, 0 < probabilities (fillMoments q p0 x) I}
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun I =>
    isOpen_lt continuous_const ((continuous_apply I).comp hcont))

private theorem fill_convex_combination {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x y : High n q → ℝ) (a b : ℝ) (hab : a + b = 1) :
    fillMoments q p0 (a • x + b • y) =
      a • fillMoments q p0 x + b • fillMoments q p0 y := by
  funext I
  dsimp [fillMoments]
  split_ifs
  · rw [← add_mul, hab, one_mul]
  · rfl

/-- The positive high-moment domain is convex for every compatible fixed low-moment vector. -/
private theorem positive_domain_convex {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Convex ℝ (positiveDomain q p0) := by
  intro x hx y hy a b ha hb hab
  change ∀ I, 0 < probabilities (fillMoments q p0 (a • x + b • y)) I
  rw [fill_convex_combination q p0 x y a b hab]
  have he : probabilities (a • fillMoments q p0 x + b • fillMoments q p0 y) =
      a • probabilities (fillMoments q p0 x) + b • probabilities (fillMoments q p0 y) :=
    (momentLinearEquiv n).symm.map_add _ _ |>.trans
      (congrArg₂ (· + ·) ((momentLinearEquiv n).symm.map_smul a _)
        ((momentLinearEquiv n).symm.map_smul b _))
  rw [he]
  intro I
  change 0 < a * probabilities (fillMoments q p0 x) I +
    b * probabilities (fillMoments q p0 y) I
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx I)) (mul_nonneg hb (hy I).le)
  · have hb' : b = 1 := by linarith
    simpa [← ha', hb'] using hy I

/-- Full positive representatives with the prescribed low moments. -/
abbrev Representative {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :=
  ProbabilityFibre q p0 × (Pattern n → AddCircle (2 * Real.pi))

/-- Reduction identifies exactly the common and low-moment phase actions, at unchanged p. -/
def reductionSetoid {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Setoid (Representative q p0) where
  r a b := a.1 = b.1 ∧ PhaseOrbit n q (AddCircle (2 * Real.pi)) a.2 b.2
  iseqv := by
    refine ⟨fun _ => ⟨rfl, (phaseSetoid n q _).refl _⟩, ?_, ?_⟩
    · intro a b h; exact ⟨h.1.symm, (phaseSetoid n q _).symm h.2⟩
    · intro a b c h k; exact ⟨h.1.trans k.1, (phaseSetoid n q _).trans h.2 k.2⟩

/-- Global coordinates for the actual positive fixed-moment phase quotient. -/
def reductionEquiv {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Quotient (reductionSetoid q p0) ≃
      positiveDomain q p0 × (High n q → AddCircle (2 * Real.pi)) where
  toFun := Quotient.lift
    (fun a => (probabilityFibreEquiv q p0 a.1, highPhases a.2))
    (by
      intro a b h
      exact Prod.ext (congrArg (probabilityFibreEquiv q p0) h.1)
        ((orbit_iff_high_phases a.2 b.2).mp h.2))
  invFun z := Quotient.mk _
    ((probabilityFibreEquiv q p0).symm z.1,
      (phaseEquiv n _).symm (highEmbedding n q _ z.2))
  left_inv := by
    intro z
    refine Quotient.inductionOn z (fun a => ?_)
    apply Quotient.sound
    refine ⟨(probabilityFibreEquiv q p0).symm_apply_apply _, ?_⟩
    apply (orbit_iff_high_phases _ _).mpr
    funext T
    change phaseEquiv n _ ((phaseEquiv n _).symm (highEmbedding n q _ _)) T.val = _
    rw [AddEquiv.apply_symm_apply]
    simp [highEmbedding, T.property, highPhases]
  right_inv := by
    rintro ⟨x, phi⟩
    apply Prod.ext
    · exact (probabilityFibreEquiv q p0).apply_symm_apply x
    · funext T
      change phaseEquiv n _ ((phaseEquiv n _).symm (highEmbedding n q _ phi)) T.val = _
      rw [AddEquiv.apply_symm_apply]
      simp [highEmbedding, T.property]

end D5.S3.Quantum.Fibers.LegalChainMomentQuotient

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentTopology
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open scoped BigOperators

private theorem continuous_act {ι G : Type*} [Fintype ι] [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] (A : Matrix ι ι ℤ) :
    Continuous (act A : (ι → G) → ι → G) := by
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ (fun j _ => (continuous_apply j).zsmul (A i j))

private theorem continuous_high_phases {n q : ℕ} {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    Continuous (highPhases (n := n) (q := q) (G := G)) := by
  apply continuous_pi
  intro T
  exact (continuous_apply T.val).comp (continuous_act (signedIncidence n).transpose)

private theorem continuous_high_embedding (n q : ℕ) (G : Type*) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    Continuous (highEmbedding n q G) := by
  apply continuous_pi
  intro I
  change Continuous (fun x : High n q → G => if h : q < I.val.card then x ⟨I, h⟩ else 0)
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- The positive fibre coordinates and inverse are continuous in the actual subspace topologies. -/
def probabilityFibreHomeomorph {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    ProbabilityFibre q p0 ≃ₜ positiveDomain q p0 where
  toEquiv := probabilityFibreEquiv q p0
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro T
    exact (continuous_apply T.val).comp
      ((momentLinearEquiv n).toContinuousLinearEquiv.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (momentLinearEquiv n).symm.toContinuousLinearEquiv.continuous.comp
      ((D5.S3.Quantum.Fibers.LegalChainMomentQuotient.continuous_fill q p0).comp continuous_subtype_val)

/-- The set quotient equivalence is a homeomorphism for the quotient topology. -/
def reductionHomeomorph {n : ℕ} (q : ℕ) (p0 : PositiveProbability n) :
    Quotient (reductionSetoid q p0) ≃ₜ
      positiveDomain q p0 × (High n q → AddCircle (2 * Real.pi)) where
  toEquiv := reductionEquiv q p0
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact ((probabilityFibreHomeomorph q p0).continuous.comp continuous_fst).prodMk
      (continuous_high_phases.comp continuous_snd)
  continuous_invFun := by
    apply continuous_quotient_mk'.comp
    exact ((probabilityFibreHomeomorph q p0).symm.continuous.comp continuous_fst).prodMk
      ((continuous_act (incidence n).transpose).comp
        ((continuous_high_embedding n q (AddCircle (2 * Real.pi))).comp continuous_snd))

/-- The ordinary real lifts of all surviving phase angles. -/
def angleCover (n q : ℕ) (theta : High n q → ℝ) : High n q → AddCircle (2 * Real.pi) :=
  fun I => (theta I : AddCircle (2 * Real.pi))

/-- Around each real phase lift the ordinary period projection is a local homeomorphism. -/
private theorem angle_cover_local {n q : ℕ} : IsLocalHomeomorph (angleCover n q) := by
  classical
  intro theta
  have he := AddCircle.isLocalHomeomorph_coe (2 * Real.pi)
  choose e hmem hfun using (fun I : High n q => he (theta I))
  refine ⟨OpenPartialHomeomorph.pi e, ?_, ?_⟩
  · exact fun I _ => hmem I
  · funext t I
    exact congrFun (hfun I) (t I)

/-- Real phase lifts reconstruct actual quotient states using the global inverse coordinates. -/
def quotientCover {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (z : positiveDomain q p0 × (High n q → ℝ)) : Quotient (reductionSetoid q p0) :=
  (reductionHomeomorph q p0).symm (z.1, angleCover n q z.2)

/-- Every actual quotient point has a real lift with exactly the standard integral phase periods. -/
private theorem quotient_cover_fibre {n : ℕ} (q : ℕ) (p0 : PositiveProbability n)
    (x y : positiveDomain q p0 × (High n q → ℝ)) :
    quotientCover q p0 x = quotientCover q p0 y ↔
      x.1 = y.1 ∧ ∃ k : High n q → ℤ,
        ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ) := by
  rw [quotientCover, quotientCover, (reductionHomeomorph q p0).symm.injective.eq_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, htheta⟩
    refine ⟨hxy, ?_⟩
    have h : ∀ T, ∃ k : ℤ, x.2 T - y.2 T = 2 * Real.pi * (k : ℝ) := by
      intro T
      exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (congrFun htheta T)
    exact Classical.axiomOfChoice h
  · rintro ⟨hxy, k, hk⟩
    refine ⟨hxy, ?_⟩
    funext T
    exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr ⟨k T, hk T⟩

end D5.S3.Quantum.Fibers.LegalChainMomentTopology

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open scoped BigOperators

abbrev V (n : ℕ) := Pattern n → ℝ
abbrev C (n : ℕ) := Pattern n → ℂ

/-- Real probability evaluation on a probability-phase lift. -/
def pEval (n : ℕ) (I : Pattern n) : (V n × V n) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj I).comp (ContinuousLinearMap.fst ℝ (V n) (V n))

/-- Real phase evaluation on a probability-phase lift. -/
def thetaEval (n : ℕ) (I : Pattern n) : (V n × V n) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj I).comp (ContinuousLinearMap.snd ℝ (V n) (V n))

/-- The literal polar map with the convention psi = sqrt(p) exp(-i theta). -/
def polarMap (n : ℕ) (x : V n × V n) : C n :=
  fun I => (Real.sqrt (x.1 I) : ℂ) * Complex.exp (-Complex.I * (x.2 I : ℂ))

/-- The derivative obtained from the square root, complex exponential, and product rules. -/
def polarDerivative (n : ℕ) (x : V n × V n) : (V n × V n) →L[ℝ] C n :=
  ContinuousLinearMap.pi fun I =>
    (Real.sqrt (x.1 I) : ℂ) •
        (Complex.exp (-Complex.I * (x.2 I : ℂ)) •
          ((-Complex.I) • (Complex.ofRealCLM.comp (thetaEval n I)))) +
      Complex.exp (-Complex.I * (x.2 I : ℂ)) •
        (Complex.ofRealCLM.comp ((1 / (2 * Real.sqrt (x.1 I))) • pEval n I))

/-- The stated polar tangent is the actual Frechet derivative on the positive amplitude domain. -/
private theorem polar_hasFDerivAt (n : ℕ) (x : V n × V n) (hx : ∀ I, 0 < x.1 I) :
    HasFDerivAt (polarMap n) (polarDerivative n x) x := by
  apply hasFDerivAt_pi.mpr
  intro I
  have hp := ((pEval n I).hasFDerivAt (x := x)).sqrt (hx I).ne'
  have hpC := Complex.ofRealCLM.hasFDerivAt.comp x hp
  have ht := ((Complex.ofRealCLM.comp (thetaEval n I)).hasFDerivAt (x := x)).const_mul
    (-Complex.I)
  have he := ht.cexp
  convert! hpC.mul he using 1 <;> simp [polarMap, polarDerivative, pEval, thetaEval]

/-- The amplitude on the actual phase circles, without a choice of real lifts. -/
def polarTorusMap (n : ℕ) (p : V n)
    (theta : Pattern n → Real.Angle) : C n :=
  fun I => (Real.sqrt (p I) : ℂ) * ((-theta I : Real.Angle).toCircle : ℂ)

private theorem polar_torus_lift (n : ℕ) (p theta : V n) :
    polarMap n (p, theta) = polarTorusMap n p (fun I => (theta I : Real.Angle)) := by
  ext I
  change (Real.sqrt (p I) : ℂ) * Complex.exp (-Complex.I * (theta I : ℂ)) =
    (Real.sqrt (p I) : ℂ) * ((-(theta I : Real.Angle)).toCircle : ℂ)
  rw [← Real.Angle.coe_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  congr 2
  push_cast
  ring

private theorem polar_derivative_apply (n : ℕ) (x d : V n × V n) (I : Pattern n) :
    polarDerivative n x d I = Complex.exp (-Complex.I * (x.2 I : ℂ)) *
      ((d.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) -
        Complex.I * (Real.sqrt (x.1 I) : ℂ) * (d.2 I : ℂ)) := by
  simp [polarDerivative, pEval, thetaEval, Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem phase_exp_cancel (theta : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * (theta : ℂ))) *
      Complex.exp (-Complex.I * (theta : ℂ)) = 1 := by
  change (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (-Complex.I * (theta : ℂ)) + -Complex.I * (theta : ℂ) = 0 := by
    simp
  simpa using congrArg Complex.exp h

private theorem polar_inner_coordinate (n : ℕ) (x d : V n × V n)
    (hx : ∀ I, 0 < x.1 I) (I : Pattern n) :
    (starRingEnd ℂ) (polarMap n x I) * polarDerivative n x d I =
      ((d.1 I / 2 : ℝ) : ℂ) - Complex.I * ((x.1 I * d.2 I : ℝ) : ℂ) := by
  rw [polarMap, polar_derivative_apply]
  rw [map_mul]
  have he := phase_exp_cancel (x.2 I)
  have hs : (Real.sqrt (x.1 I) : ℂ) ^ 2 = (x.1 I : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hx I).le
  have hn : (Real.sqrt (x.1 I) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (hx I)).ne'
  simp only [Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.star_def]
  calc
    _ = ((starRingEnd ℂ) (Complex.exp (-Complex.I * (x.2 I : ℂ))) *
          Complex.exp (-Complex.I * (x.2 I : ℂ))) *
        ((Real.sqrt (x.1 I) : ℂ) *
          ((d.1 I : ℂ) / (2 * (Real.sqrt (x.1 I) : ℂ)) -
            Complex.I * (Real.sqrt (x.1 I) : ℂ) * (d.2 I : ℂ))) := by ring
    _ = _ := by rw [he, one_mul]; field_simp; rw [hs]; ring

/-- The canonical one-form is computed from the actual amplitude derivative. -/
def amplitudeOneForm (n : ℕ) (x d : V n × V n) : ℝ :=
  -(∑ I, (starRingEnd ℂ) (polarMap n x I) * polarDerivative n x d I).im

private theorem amplitude_one_form (n : ℕ) (x d : V n × V n)
    (hx : ∀ I, 0 < x.1 I) : amplitudeOneForm n x d = ∑ I, x.1 I * d.2 I := by
  simp only [amplitudeOneForm, polar_inner_coordinate n x d hx, Complex.im_sum,
    Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, add_zero, zero_add, zero_sub, Finset.sum_neg_distrib,
    neg_neg]

private theorem dual_pairing (n : ℕ) (p v : V n) :
    ∑ I, p I * v I = ∑ T, moments p T * phases v T := by
  have hv : originalPhases (phases v) = v := (phaseEquiv n ℝ).symm_apply_apply v
  conv_lhs => rw [← hv]
  simp only [originalPhases, moments, act, Matrix.transpose_apply, incidence]
  simp only [ite_smul, one_smul, zero_smul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro I _
  split_ifs <;> simp

/-- With the negative phase convention the canonical one-form has the positive moment sign. -/
private theorem canonical_one_form_moments (n : ℕ) (x d : V n × V n)
    (hx : ∀ I, 0 < x.1 I) :
    amplitudeOneForm n x d = ∑ T, moments x.1 T * phases d.2 T := by
  rw [amplitude_one_form n x d hx, dual_pairing]

/-- The prescribed source two-form, evaluated on actual probability-phase tangent vectors. -/
def sourceTwoForm (n : ℕ) (d e : V n × V n) : ℝ :=
  ∑ I, (d.2 I * e.1 I - e.2 I * d.1 I)

/-- The source two-form transforms by the actual derivatives of the moment and phase maps. -/
private theorem source_two_form_moments (n : ℕ) (d e : V n × V n) :
    sourceTwoForm n d e =
      ∑ T, (phases d.2 T * moments e.1 T - phases e.2 T * moments d.1 T) := by
  calc
    sourceTwoForm n d e = (∑ I, e.1 I * d.2 I) - (∑ I, d.1 I * e.2 I) := by
      simp [sourceTwoForm, Finset.sum_sub_distrib, mul_comm]
    _ = (∑ T, moments e.1 T * phases d.2 T) -
        (∑ T, moments d.1 T * phases e.2 T) :=
      congrArg₂ (· - ·) (dual_pairing n e.1 d.2) (dual_pairing n d.1 e.2)
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro T _
      ring

/-- The standard projective Hermitian expression evaluated on polar tangent vectors. -/
def projectiveTwoForm (n : ℕ) (x d e : V n × V n) : ℝ :=
  2 * ((∑ I, (starRingEnd ℂ) (polarDerivative n x d I) * polarDerivative n x e I) -
    (starRingEnd ℂ) (∑ I, (starRingEnd ℂ) (polarMap n x I) * polarDerivative n x d I) *
      (∑ I, (starRingEnd ℂ) (polarMap n x I) * polarDerivative n x e I)).im

private theorem polar_tangent_inner_im (n : ℕ) (x d e : V n × V n)
    (hx : ∀ I, 0 < x.1 I) (I : Pattern n) :
    2 * ((starRingEnd ℂ) (polarDerivative n x d I) * polarDerivative n x e I).im =
      d.2 I * e.1 I - e.2 I * d.1 I := by
  rw [polar_derivative_apply, polar_derivative_apply]
  have hs : Real.sqrt (x.1 I) ≠ 0 := (Real.sqrt_pos.mpr (hx I)).ne'
  have hexp := phase_exp_cancel (x.2 I)
  have hprod :
      (starRingEnd ℂ) (Complex.exp (-Complex.I * (x.2 I : ℂ)) *
        ((d.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) -
          Complex.I * (Real.sqrt (x.1 I) : ℂ) * (d.2 I : ℂ))) *
      (Complex.exp (-Complex.I * (x.2 I : ℂ)) *
        ((e.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) -
          Complex.I * (Real.sqrt (x.1 I) : ℂ) * (e.2 I : ℂ))) =
      (starRingEnd ℂ) (((d.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) : ℂ) -
          Complex.I * (Real.sqrt (x.1 I) : ℂ) * (d.2 I : ℂ)) *
        (((e.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) : ℂ) -
          Complex.I * (Real.sqrt (x.1 I) : ℂ) * (e.2 I : ℂ)) := by
    rw [map_mul]
    calc
      _ = ((starRingEnd ℂ) (Complex.exp (-Complex.I * (x.2 I : ℂ))) *
          Complex.exp (-Complex.I * (x.2 I : ℂ))) *
            ((starRingEnd ℂ) (((d.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) : ℂ) -
              Complex.I * (Real.sqrt (x.1 I) : ℂ) * (d.2 I : ℂ)) *
            (((e.1 I / (2 * Real.sqrt (x.1 I)) : ℝ) : ℂ) -
              Complex.I * (Real.sqrt (x.1 I) : ℂ) * (e.2 I : ℂ))) := by ring
      _ = _ := by rw [hexp, one_mul]
  rw [hprod]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  field_simp
  <;> ring

/-- On normalized probability tangents the projective correction has zero imaginary part. -/
private theorem projective_two_form_source (n : ℕ) (x d e : V n × V n)
    (hx : ∀ I, 0 < x.1 I) (hd : ∑ I, d.1 I = 0) (he : ∑ I, e.1 I = 0) :
    projectiveTwoForm n x d e = sourceTwoForm n d e := by
  have hinner : ∀ v : V n × V n, (∑ I, v.1 I = 0) →
      (∑ I, (starRingEnd ℂ) (polarMap n x I) * polarDerivative n x v I) =
        -Complex.I * ((∑ I, x.1 I * v.2 I : ℝ) : ℂ) := by
    intro v hv
    simp_rw [polar_inner_coordinate n x v hx]
    rw [Finset.sum_sub_distrib, ← Complex.ofReal_sum, ← Finset.sum_div, hv, zero_div,
      Complex.ofReal_zero, zero_sub, ← Finset.mul_sum, ← Complex.ofReal_sum]
    ring
  rw [projectiveTwoForm, hinner d hd, hinner e he]
  have hc : ((starRingEnd ℂ) (-Complex.I * ((∑ I, x.1 I * d.2 I : ℝ) : ℂ)) *
      (-Complex.I * ((∑ I, x.1 I * e.2 I : ℝ) : ℂ))).im = 0 := by simp
  rw [Complex.sub_im, hc, sub_zero, Complex.im_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun I _ => polar_tangent_inner_im n x d e hx I)

end D5.S3.Quantum.Fibers.LegalChainMomentGeometry

end

noncomputable section
namespace D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
open D5.S3.Quantum.Fibers.LegalChainMomentQuotient
open D5.S3.Quantum.Fibers.LegalChainMomentTopology
open D5.S3.Quantum.Fibers.LegalChainMomentGeometry
open scoped BigOperators

/-- Integral inversion, effective occupation orbits, positive domains and actual polar forms. -/
theorem legal_chain_coordinate_laws (n q : ℕ) :
    signedIncidence n * incidence n = 1 ∧ incidence n * signedIncidence n = 1 ∧
    (∀ (G : Type) [AddCommGroup G] (t : Low n q → G),
      occupationAction n q G t = actionHom n q G t) ∧
    (∀ (G : Type) [AddCommGroup G] (theta eta : Pattern n → G),
      PhaseOrbit n q G theta eta ↔ highPhases (q := q) theta = highPhases (q := q) eta) ∧
    (∀ p0 : PositiveProbability n, (positiveDomain q p0).Nonempty ∧
      IsOpen (positiveDomain q p0) ∧ Convex ℝ (positiveDomain q p0)) ∧
    (∀ (p0 : PositiveProbability n) (x y : positiveDomain q p0 × (High n q → ℝ)),
      quotientCover q p0 x = quotientCover q p0 y ↔ x.1 = y.1 ∧
        ∃ k : High n q → ℤ, ∀ T, x.2 T - y.2 T = 2 * Real.pi * (k T : ℝ)) ∧
    (∀ (x d : V n × V n), (∀ I, 0 < x.1 I) →
      amplitudeOneForm n x d = ∑ T, moments x.1 T * phases d.2 T) ∧
    (∀ d e : V n × V n, sourceTwoForm n d e =
      ∑ T, (phases d.2 T * moments e.1 T - phases e.2 T * moments d.1 T)) ∧
    (∀ (x d e : V n × V n), (∀ I, 0 < x.1 I) → (∑ I, d.1 I = 0) →
      (∑ I, e.1 I = 0) → projectiveTwoForm n x d e = sourceTwoForm n d e) ∧
    (∀ (x : V n × V n), (∀ I, 0 < x.1 I) →
      HasFDerivAt (polarMap n) (polarDerivative n x) x) ∧
    (∀ p theta : V n, polarMap n (p, theta) =
      polarTorusMap n p (fun I => (theta I : Real.Angle))) ∧
    IsLocalHomeomorph (angleCover n q) := by
  exact ⟨signed_mul_incidence n, incidence_mul_signed n,
    occupation_action_eq n q, fun G _ theta eta => orbit_iff_high_phases theta eta,
    fun p0 => ⟨positive_domain_nonempty q p0, positive_domain_open q p0,
      positive_domain_convex q p0⟩,
    quotient_cover_fibre q, canonical_one_form_moments n, source_two_form_moments n,
    projective_two_form_source n, polar_hasFDerivAt n, polar_torus_lift n,
    angle_cover_local⟩

end D5.S3.Quantum.Fibers.LegalChainMomentCoordinates
end
