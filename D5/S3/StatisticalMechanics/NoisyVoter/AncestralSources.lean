/- GID: D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/AncestralSources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ancestral sources give a degree-independent native repetition variance bound. -/

/-
proof_shape: native_source: content; uniform_variance_lower: content
admission_basis: escape-witness
escape_witness: native_source; covariance_domination
The native reconstruction and degree-independent lower bound supply prerequisites of
noisy-voter Theorem 3.2. No complete optimal-constant bracket is asserted here.
Reuse: RepetitionVarianceLinear supplies the original Model, nvm, W and nvm_measurable;
Mathlib supplies independence of coordinate subfamilies, product integration and covariance sums.
The source histories and source-selected pair/four-opinion moments are established on the
same original probability space. No moment identity or native bridge is an extra hypothesis.
Rows: declaration | proof_shape | escape_witness | live direct consumer(s).
Constructions are definitions, not new theorem classifications.
Label | construction | none | source, coin, possibleSources
birth | construction | none | source_birth_le, survives_iff_old_source
coin | construction | none | native_source, fixed_pair_sign_mean, native_pair_sign_mean
source | construction | none | native_source, source_birth_le, source_measurable
native_source | content | native_source | native_pair_sign_mean, native_four_sign_mean
source_birth_le | content | source_birth_le | survives_iff_old_source, collision_requires_survival
survives | construction | none | survives_iff_old_source, survival_probability
survives_iff_old_source | content | survives_iff_old_source | collision_requires_survival, survives_measurable, survives_fillPast
collision_requires_survival | content | source_birth_le | collision_probability_le
labelMeasurable | bind-only | none | source_measurable, sources_independent_coins
labelMeasurableSingleton | bind-only | none | source_eq_measurable, native_four_sign_mean
source_measurable | content | source_measurable | source_eq_measurable, survives_measurable, sources_independent_coins
coordinateTime | construction | none | fillPast, fresh_pair_independent_survival
source_past | content | source_past | survives_fillPast, sources_independent_coins
possibleSources | construction | none | source_mem_possible, source_eq_measurable, native_pair_sign_mean, native_four_sign_mean
source_mem_possible | content | source_mem_possible | source_eq_measurable, native_pair_sign_mean, native_four_sign_mean
source_eq_measurable | content | source_mem_possible | native_pair_sign_mean, C_memLp, C_mean, covariance_domination
survives_measurable | content | source_measurable | fresh_pair_independent_survival, survival_probability
defaultCoordinate | construction | none | fillPast
fillPast | construction | none | fillPast_measurable, survives_fillPast, fresh_pair_independent_survival
fillPast_measurable | bind-only | none | fresh_pair_independent_survival
survives_fillPast | content | source_past | fresh_pair_independent_survival
fresh_pair_independent_survival | content | source_past | survival_probability
survival_probability | content | survival_probability | collision_probability_le
collision_probability_le | content | survival_probability | uniform_variance_lower
isControl | construction | none | fillControls, sources_independent_coins
fillControls | construction | none | fillControls_measurable, sources_independent_coins
fillControls_measurable | bind-only | none | sources_independent_coins
sources_independent_coins | content | source_past | native_pair_sign_mean, native_four_sign_mean
labelCoordinate | construction | none | readCoin, labelCoordinate_injective, coins_independent
readCoin | construction | none | coins_independent
labelCoordinate_injective | bind-only | none | coins_independent
coins_independent | bind-only | none | fixed_pair_sign_mean, fixed_four_sign_mean
coin_hasLaw | bind-only | none | fixed_pair_sign_mean
finite_selector_integral | bind-only | none | native_pair_sign_mean, native_four_sign_mean
fixed_pair_sign_mean | bind-only | none | native_pair_sign_mean, fixed_four_sign_mean
native_pair_sign_mean | content | native_source | covariance_domination, diagonal_difference
fixed_four_sign_mean | bind-only | none | native_four_sign_mean
evenPairing | construction | none | native_four_sign_mean, covariance_domination
native_four_sign_mean | content | native_source | covariance_domination
Z | construction | none | Z_memLp, covariance_domination, diagonal_difference, native_variance_lower
C | construction | none | C_memLp, C_mean, covariance_domination, diagonal_difference, native_variance_lower
Z_memLp | bind-only | none | covariance_domination, diagonal_difference, native_variance_lower
C_memLp | content | source_mem_possible | covariance_domination, diagonal_difference, native_variance_lower
C_mean | content | source_mem_possible | covariance_domination, diagonal_difference
covariance_domination | content | native_four_sign_mean | native_variance_lower
diagonal_difference | content | native_pair_sign_mean | native_variance_lower
native_variance_lower | content | covariance_domination | uniform_variance_lower
uniform_variance_lower | content | covariance_domination | terminal original-theorem prerequisite
-/

import D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear

/-! # Actual ancestral sources of the synchronous noisy voter recursion -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

open RepetitionVarianceLinear

variable {V Ω : Type} {G : SimpleGraph V}

/-- Initial opinions and positive-time fresh opinions have disjoint labels. -/
abbrev Label (V : Type) := V ⊕ (ℕ+ × V)

def birth : Label V → ℕ
  | .inl _ => 0
  | .inr p => p.1.val

def coin (x : (i : Coord V) → Ω → Value G i) : Label V → Ω → Bool
  | .inl v => x (.initial v)
  | .inr p => x (.fresh p.1.val p.2)

/-- The backward history of the native synchronous recursion, stopped at its first refresh. -/
def source (x : (i : Coord V) → Ω → Value G i) : ℕ → V → Ω → Label V
  | 0, v, _ => .inl v
  | n+1, v, ω => if x (.refresh (n+1) v) ω then .inr (⟨n+1, Nat.succ_pos n⟩, v)
      else source x n (x (.choice (n+1) v) ω).val ω

theorem native_source (x : (i : Coord V) → Ω → Value G i) :
    ∀ n v ω, nvm x n v ω = coin x (source x n v ω) ω := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro v ω
    simp only [nvm, source]
    split_ifs
    · rfl
    · exact ih _ _

private theorem source_birth_le (x : (i : Coord V) → Ω → Value G i) :
    ∀ n v ω, birth (source x n v ω) ≤ n := by
  intro n
  induction n with
  | zero => intros; exact Nat.le_refl 0
  | succ n ih =>
    intro v ω
    simp only [source]
    split_ifs
    · exact Nat.le_refl _
    · exact (ih _ _).trans (Nat.le_succ n)

/-- No refresh in the final k layers of a history starting at time i+k. -/
def survives (x : (i : Coord V) → Ω → Value G i) (i : ℕ) : ℕ → V → Ω → Bool
  | 0, _, _ => true
  | k+1, v, ω => if x (.refresh (i+k+1) v) ω then false
      else survives x i k (x (.choice (i+k+1) v) ω).val ω

private theorem survives_iff_old_source (x : (i : Coord V) → Ω → Value G i) (i : ℕ) :
    ∀ k v ω, survives x i k v ω = true ↔ birth (source x (i+k) v ω) ≤ i := by
  intro k
  induction k with
  | zero =>
    intro v ω
    simp only [survives, Nat.add_zero, true_iff]
    exact source_birth_le x i v ω
  | succ k ih =>
    intro v ω
    rw [show i + (k+1) = (i+k)+1 by omega]
    simp only [survives, source]
    split_ifs
    · simp [birth]
    · exact ih _ _

private theorem collision_requires_survival (x : (i : Coord V) → Ω → Value G i)
    (i d : ℕ) (u : V) (ω : Ω)
    (h : source x i u ω = source x (i+d) u ω) : survives x i d u ω = true := by
  apply (survives_iff_old_source x i d u ω).2
  rw [← h]
  exact source_birth_le x i u ω

instance labelMeasurable : MeasurableSpace (Label V) := ⊤

instance labelMeasurableSingleton : MeasurableSingletonClass (Label V) := ⟨fun _ => trivial⟩

private theorem source_measurable [G.LocallyFinite] [MeasurableSpace Ω]
    (x : (i : Coord V) → Ω → Value G i) (hx : ∀ i, Measurable (x i)) :
    ∀ n v, Measurable (source x n v) := by
  intro n
  induction n with
  | zero => intro v; exact measurable_const
  | succ n ih =>
    intro v
    have hc : Measurable (fun ω => source x n (x (.choice (n+1) v) ω).val ω) := by
      have hp : Measurable (fun p : G.neighborSet v × Ω => source x n p.1.val p.2) :=
        measurable_from_prod_countable_right (fun w => ih w.val)
      exact hp.comp ((hx (.choice (n+1) v)).prodMk measurable_id)
    exact Measurable.ite ((hx (.refresh (n+1) v)) (measurableSet_singleton true))
      measurable_const hc

def coordinateTime : Coord V → ℕ
  | .initial _ => 0
  | .fresh n _ | .refresh n _ | .choice n _ => n

private theorem source_past {Ω' : Type}
    (x : (i : Coord V) → Ω → Value G i) (y : (i : Coord V) → Ω' → Value G i) (N : ℕ)
    (ω : Ω) (ω' : Ω')
    (hr : ∀ n, n ≤ N → ∀ v, x (.refresh n v) ω = y (.refresh n v) ω')
    (hj : ∀ n, n ≤ N → ∀ v, x (.choice n v) ω = y (.choice n v) ω') :
    ∀ n, n ≤ N → ∀ v, source x n v ω = source y n v ω' := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro hn v
    simp only [source, hr (n+1) hn v, hj (n+1) hn v]
    split_ifs
    · rfl
    · exact ih (by omega) _

noncomputable def possibleSources [G.LocallyFinite] : ℕ → V → Finset (Label V)
  | 0, v => {Sum.inl v}
  | n+1, v => by
      classical
      exact insert (.inr (⟨n+1, Nat.succ_pos n⟩, v))
        ((G.neighborFinset v).biUnion (possibleSources n))

private theorem source_mem_possible [G.LocallyFinite]
    (x : (i : Coord V) → Ω → Value G i) :
    ∀ n v ω, source x n v ω ∈ possibleSources (G := G) n v := by
  classical
  intro n
  induction n with
  | zero => intros; simp [source, possibleSources]
  | succ n ih =>
    intro v ω
    simp only [source]
    split_ifs
    · simp [possibleSources]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨(x (.choice (n+1) v) ω).val,
        by rw [SimpleGraph.mem_neighborFinset]; exact (x (.choice (n+1) v) ω).property, ih _ _⟩

private theorem source_eq_measurable [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (n m : ℕ) (u v : V) :
    MeasurableSet {ω | source M.coordinate n u ω = source M.coordinate m v ω} := by
  classical
  have heq : {ω | source M.coordinate n u ω = source M.coordinate m v ω} =
      ⋃ l : ↑(possibleSources (G := G) n u),
        {ω | source M.coordinate n u ω = l.val} ∩
        {ω | source M.coordinate m v ω = l.val} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨_, source_mem_possible M.coordinate n u ω⟩, rfl, h.symm⟩
    · rintro ⟨l, h₁, h₂⟩
      exact h₁.trans h₂.symm
  rw [heq]
  exact MeasurableSet.iUnion (fun l =>
    ((source_measurable M.coordinate M.measurable_coordinate n u)
      (measurableSet_singleton l.val)).inter
    ((source_measurable M.coordinate M.measurable_coordinate m v)
      (measurableSet_singleton l.val)))


private theorem survives_measurable [G.LocallyFinite] [MeasurableSpace Ω]
    (x : (i : Coord V) → Ω → Value G i) (hx : ∀ i, Measurable (x i))
    (i k : ℕ) (v : V) : Measurable (survives x i k v) := by
  have he : survives x i k v = fun ω =>
      if birth (source x (i+k) v ω) ≤ i then true else false := by
    funext ω
    have h := survives_iff_old_source x i k v ω
    split_ifs with hh
    · exact h.2 hh
    · exact Bool.eq_false_iff.mpr (fun ht => hh (h.1 ht))
  rw [he]
  apply Measurable.ite _ measurable_const measurable_const
  exact (source_measurable x hx (i+k) v) (t := {l | birth l ≤ i}) trivial

private noncomputable def defaultCoordinate (hNbr : ∀ v, ∃ w, G.Adj v w) :
    (c : Coord V) → Value G c
  | .initial _ | .fresh _ _ | .refresh _ _ => false
  | .choice _ v => ⟨(hNbr v).choose, (hNbr v).choose_spec⟩

private noncomputable def fillPast (hNbr : ∀ v, ∃ w, G.Adj v w) (N : ℕ)
    (z : (c : {c : Coord V // coordinateTime c ≤ N}) → Value G c.val)
    (c : Coord V) : Value G c :=
  if hc : coordinateTime c ≤ N then z ⟨c, hc⟩ else defaultCoordinate hNbr c

private theorem fillPast_measurable [G.LocallyFinite]
    (hNbr : ∀ v, ∃ w, G.Adj v w) (N : ℕ) (c : Coord V) :
    Measurable (fun z => fillPast hNbr N z c) := by
  classical
  unfold fillPast
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

private theorem survives_fillPast [G.LocallyFinite]
    (hNbr : ∀ v, ∃ w, G.Adj v w)
    (x : (c : Coord V) → Ω → Value G c) (i k : ℕ) (v : V) (ω : Ω) :
    survives (fun c z => fillPast hNbr (i+k) z c) i k v
      (fun c => x c.val ω) = survives x i k v ω := by
  have hs := source_past (fun c z => fillPast hNbr (i+k) z c)
    x (i+k) (fun c => x c.val ω) ω
    (by intro n hn v; simp [fillPast, coordinateTime, hn])
    (by intro n hn v; simp [fillPast, coordinateTime, hn]) (i+k) le_rfl v
  have ha := survives_iff_old_source
    (fun c z => fillPast hNbr (i+k) z c) i k v (fun c => x c.val ω)
  have hb := survives_iff_old_source x i k v ω
  exact Bool.eq_iff_iff.mpr (ha.trans (hs ▸ hb.symm))

private theorem fresh_pair_independent_survival [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (i k : ℕ) (u v : V) :
    IndepFun (fun ω => (M.coordinate (.refresh (i+k+1) u) ω,
      M.coordinate (.choice (i+k+1) u) ω)) (survives M.coordinate i k v) P := by
  classical
  let r := Coord.refresh (i+k+1) u
  let j := Coord.choice (i+k+1) u
  let A : Set (Coord V) := {r, j}
  let B : Set (Coord V) := {c | coordinateTime c ≤ i+k}
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro c hc hb
    rcases hc with rfl | rfl <;> change i+k+1 ≤ i+k at hb <;> omega
  have hi := M.independent.indepFun_set A B hd M.measurable_coordinate
  have hm : Measurable (fun z : (c : B) → Value G c.val =>
      survives (fun c z => fillPast M.hasNeighbor (i+k) z c) i k v z) :=
    survives_measurable _ (fillPast_measurable M.hasNeighbor (i+k)) i k v
  have hp : Measurable (fun z : (c : A) → Value G c.val =>
      (z ⟨r, by simp [A]⟩, z ⟨j, by simp [A]⟩)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hh := hi.comp hp hm
  convert hh using 1
  · rfl
  · funext ω
    exact (survives_fillPast M.hasNeighbor M.coordinate i k v ω).symm

private theorem survival_probability [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (i : ℕ) :
    ∀ k u, P {ω | survives M.coordinate i k u ω = true} =
      (unitInterval.toNNReal (unitInterval.symm M.ε) : ℝ≥0∞) ^ k := by
  classical
  letI := M.probability
  let q : ℝ≥0∞ := unitInterval.toNNReal (unitInterval.symm M.ε)
  intro k
  induction k with
  | zero => intro u; simp [survives]
  | succ k ih =>
    intro u
    let R := M.coordinate (.refresh (i+k+1) u)
    let J := M.coordinate (.choice (i+k+1) u)
    let A (v : G.neighborSet u) : Set Ω :=
      {ω | R ω = false ∧ J ω = v ∧ survives M.coordinate i k v.val ω = true}
    have hA (v : G.neighborSet u) : MeasurableSet (A v) :=
      ((M.measurable_coordinate (.refresh (i+k+1) u))
        (measurableSet_singleton false)).inter
        (((M.measurable_coordinate (.choice (i+k+1) u)))
          (measurableSet_singleton v) |>.inter
          ((survives_measurable M.coordinate M.measurable_coordinate i k v.val)
            (measurableSet_singleton true)))
    have hd : Pairwise (fun v w => Disjoint (A v) (A w)) := by
      intro v w hvw
      apply Set.disjoint_left.mpr
      intro ω hv hw
      exact hvw (hv.2.1.symm.trans hw.2.1)
    have hUnion : {ω | survives M.coordinate i (k+1) u ω = true} = ⋃ v, A v := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A, survives, R, J]
      split_ifs with hr
      · simp [hr]
      · have hf : M.coordinate (.refresh (i+k+1) u) ω = false := Bool.eq_false_iff.mpr hr
        simp only [hf, true_and]
        constructor
        · intro h
          exact ⟨M.coordinate (.choice (i+k+1) u) ω, rfl, h⟩
        · rintro ⟨v, hv, hs⟩
          simpa only [hv] using hs
    have hR : P {ω | R ω = false} = q := by
      simpa [R, coordinateLaw, bernoulliMeasure_apply, q] using
        (M.laws (.refresh (i+k+1) u)).measure_eq
          (p := fun b => b = false) (measurableSet_singleton false)
    have hprob (v : G.neighborSet u) : P (A v) = q * P {ω | J ω = v} * q^k := by
      have h1 := (fresh_pair_independent_survival P M i k u v.val).measure_inter_preimage_eq_mul
          ({false} ×ˢ {v}) {true}
          ((measurableSet_singleton false).prod (measurableSet_singleton v))
          (measurableSet_singleton true)
      have h2 := (M.independent.indepFun (show Coord.refresh (i+k+1) u ≠
          Coord.choice (i+k+1) u by simp)).measure_inter_preimage_eq_mul {false} {v}
            (measurableSet_singleton false) (measurableSet_singleton v)
      change P {ω | (R ω = false ∧ J ω = v) ∧ survives M.coordinate i k v.val ω = true} =
        P {ω | R ω = false ∧ J ω = v} * P {ω | survives M.coordinate i k v.val ω = true} at h1
      change P {ω | R ω = false ∧ J ω = v} = P {ω | R ω = false} * P {ω | J ω = v} at h2
      have he : A v = {ω | (R ω = false ∧ J ω = v) ∧
          survives M.coordinate i k v.val ω = true} := by ext; simp [A, and_assoc]
      rw [he, h1, ih, h2, hR]
    have hsum : (∑ v : G.neighborSet u, P {ω | J ω = v}) = 1 := by
      simpa [Set.preimage, J] using
        sum_measure_preimage_singleton (μ := P) Finset.univ
          (fun v _ => (M.measurable_coordinate (.choice (i+k+1) u))
            (measurableSet_singleton v))
    rw [hUnion, measure_iUnion hd hA, tsum_fintype]
    simp_rw [hprob]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]
    simpa only [mul_comm] using (pow_succ q k).symm

private theorem collision_probability_le [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (i d : ℕ) (u : V) :
    P {ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω} ≤
      (unitInterval.toNNReal (unitInterval.symm M.ε) : ℝ≥0∞) ^ d := by
  rw [← survival_probability P M i d u]
  apply measure_mono
  intro ω h
  exact collision_requires_survival M.coordinate i d u ω h

def isControl : Coord V → Prop
  | .initial _ | .fresh _ _ => False
  | .refresh _ _ | .choice _ _ => True

private def fillControls (z : (c : {c : Coord V // isControl c}) → Value G c.val) :
    (c : Coord V) → Value G c
  | .initial _ | .fresh _ _ => false
  | .refresh n v => z ⟨.refresh n v, trivial⟩
  | .choice n v => z ⟨.choice n v, trivial⟩

private theorem fillControls_measurable [G.LocallyFinite] (c : Coord V) :
    Measurable (fun z => fillControls (G := G) z c) := by
  cases c
  all_goals first | exact measurable_const | exact measurable_pi_apply _

private theorem sources_independent_coins [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) :
    IndepFun (fun ω (p : ℕ × V) => source M.coordinate p.1 p.2 ω)
      (fun ω l => coin M.coordinate l ω) P := by
  classical
  let A : Set (Coord V) := {c | isControl c}
  let B : Set (Coord V) := Aᶜ
  have hd : Disjoint A B := disjoint_compl_right
  have hi := M.independent.indepFun_set A B hd M.measurable_coordinate
  let f (z : (c : A) → Value G c.val) (p : ℕ × V) :=
    source (fun c z => fillControls z c) p.1 p.2 z
  let g (z : (c : B) → Value G c.val) (l : Label V) : Bool :=
    match l with
    | .inl v => z ⟨.initial v, by simp [B, A, isControl]⟩
    | .inr p => z ⟨.fresh p.1.val p.2, by simp [B, A, isControl]⟩
  have hf : Measurable f := measurable_pi_iff.mpr (fun p =>
    source_measurable _ fillControls_measurable p.1 p.2)
  have hg : Measurable g := measurable_pi_iff.mpr (by intro l; cases l <;> exact measurable_pi_apply _)
  have hh := hi.comp hf hg
  convert hh using 1
  · funext ω p
    exact (source_past (fun c (z : (c : A) → Value G c.val) => fillControls z c)
      M.coordinate p.1 (fun c : A => M.coordinate c.val ω) ω
      (by intros; rfl) (by intros; rfl) p.1 le_rfl p.2).symm
  · funext ω l
    cases l <;> rfl

def labelCoordinate : Label V → Coord V
  | .inl v => .initial v
  | .inr p => .fresh p.1.val p.2

private def readCoin (l : Label V) : Value G (labelCoordinate l) → Bool := by
  cases l <;> exact id

private theorem labelCoordinate_injective : Function.Injective (labelCoordinate (V := V)) := by
  intro a b h
  cases a with
  | inl v => cases b <;> simpa [labelCoordinate] using h
  | inr p =>
    cases b with
    | inl v => simp [labelCoordinate] at h
    | inr r =>
      simp only [labelCoordinate, Coord.fresh.injEq] at h
      congr 1
      exact Prod.ext (Subtype.ext h.1) h.2

private theorem coins_independent [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) : iIndepFun (coin M.coordinate) P := by
  have h := (M.independent.precomp labelCoordinate_injective).comp
    (fun l => readCoin (G := G) l) (by intro l; cases l <;> exact measurable_id)
  convert h using 1
  funext l ω
  cases l <;> rfl

private theorem coin_hasLaw [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (l : Label V) :
    HasLaw (coin M.coordinate l)
      (bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval)) P := by
  cases l with
  | inl v => exact M.laws (.initial v)
  | inr p => exact M.laws (.fresh p.1.val p.2)

end D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources


open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

open RepetitionVarianceLinear
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

variable {V Ω : Type} {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace Ω]

private theorem finite_selector_integral {α β : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → α) (X : Ω → β)
    (hA : Measurable A) (hX : Measurable X) (hi : IndepFun A X P)
    (s : Finset α) (hs : ∀ ω, A ω ∈ s) (f : α → β → ℝ) (C : ℝ)
    (hf : ∀ a ∈ s, Measurable (f a)) (hb : ∀ a ∈ s, ∀ x, ‖f a x‖ ≤ C) :
    (∫ ω, f (A ω) (X ω) ∂P) =
      ∑ a ∈ s, P.real {ω | A ω = a} * ∫ ω, f a (X ω) ∂P := by
  classical
  have hrepr (ω : Ω) : f (A ω) (X ω) =
      ∑ a ∈ s, if A ω = a then f a (X ω) else 0 := by
    rw [Finset.sum_eq_single_of_mem (A ω) (hs ω)]
    · simp
    · intro b hb hba; simp [Ne.symm hba]
  simp_rw [hrepr]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    have hφ : Measurable (fun b : α => if b = a then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_singleton a) measurable_const measurable_const
    have he := hi.integral_fun_comp_mul_comp hA.aemeasurable hX.aemeasurable
      hφ.aestronglyMeasurable (hf a ha).aestronglyMeasurable
    have hind : (∫ ω, if A ω = a then (1 : ℝ) else 0 ∂P) = P.real {ω | A ω = a} := by
      simpa [Set.indicator_apply, Set.preimage] using
        integral_indicator_one (hA (measurableSet_singleton a))
    simpa only [ite_mul, one_mul, zero_mul, hind] using he
  · intro a ha
    exact (MemLp.of_bound
      (Measurable.ite (hA (measurableSet_singleton a)) ((hf a ha).comp hX)
        measurable_const).aestronglyMeasurable (max C 0)
      (Eventually.of_forall (by
        intro ω
        split_ifs
        · exact (hb a ha _).trans (le_max_left _ _)
        · simpa only [norm_zero] using le_max_right C 0))).integrable one_le_two

private theorem fixed_pair_sign_mean [DecidableEq V]
    (P : Measure Ω) (M : Model G P) (a b : Label V) :
    (∫ ω, sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω) ∂P) =
      if a = b then 1 else 0 := by
  classical
  letI := M.probability
  by_cases hab : a = b
  · subst b
    have he (ω : Ω) : sgn (coin M.coordinate a ω) * sgn (coin M.coordinate a ω) = 1 := by
      cases coin M.coordinate a ω <;> norm_num [sgn]
    simp [he]
  · have hi := (coins_independent P M).indepFun hab
    have hm (l : Label V) : Measurable (coin M.coordinate l) := by
      cases l <;> exact M.measurable_coordinate _
    have he := hi.integral_fun_comp_mul_comp (hm a).aemeasurable (hm b).aemeasurable
      (measurable_of_finite sgn).aestronglyMeasurable
      (measurable_of_finite sgn).aestronglyMeasurable
    have hmean (l : Label V) : (∫ ω, sgn (coin M.coordinate l ω) ∂P) = 0 := by
      change (∫ ω, (sgn ∘ coin M.coordinate l) ω ∂P) = 0
      rw [(coin_hasLaw P M l).integral_comp (measurable_of_finite sgn).aestronglyMeasurable]
      norm_num [integral_bernoulliMeasure, sgn]
    simp only [hmean, mul_zero] at he
    simpa only [if_neg hab] using he

private theorem native_pair_sign_mean (P : Measure Ω) (M : Model G P) (n m : ℕ) (u v : V) :
    (∫ ω, sgn (nvm M.coordinate n u ω) * sgn (nvm M.coordinate m v ω) ∂P) =
      P.real {ω | source M.coordinate n u ω = source M.coordinate m v ω} := by
  classical
  letI := M.probability
  let A (ω : Ω) := (source M.coordinate n u ω, source M.coordinate m v ω)
  let X (ω : Ω) (l : Label V) := coin M.coordinate l ω
  have hA : Measurable A := (source_measurable M.coordinate M.measurable_coordinate n u).prodMk
    (source_measurable M.coordinate M.measurable_coordinate m v)
  have hX : Measurable X := measurable_pi_iff.mpr (by
    intro l; cases l <;> exact M.measurable_coordinate _)
  have hi : IndepFun A X P := (sources_independent_coins P M).comp
    ((measurable_pi_apply (n,u)).prodMk (measurable_pi_apply (m,v))) measurable_id
  let s := (possibleSources (G := G) n u) ×ˢ (possibleSources (G := G) m v)
  have hs (ω : Ω) : A ω ∈ s := Finset.mem_product.mpr
    ⟨source_mem_possible M.coordinate n u ω, source_mem_possible M.coordinate m v ω⟩
  let f (a : Label V × Label V) (x : Label V → Bool) := sgn (x a.1) * sgn (x a.2)
  have hf (a : Label V × Label V) : Measurable (f a) :=
    ((measurable_of_finite sgn).comp (measurable_pi_apply a.1)).mul
      ((measurable_of_finite sgn).comp (measurable_pi_apply a.2))
  have hb (a : Label V × Label V) (x : Label V → Bool) : ‖f a x‖ ≤ 1 := by
    dsimp only [f]
    cases h₁ : x a.1 <;> cases h₂ : x a.2 <;> norm_num [h₁, h₂, sgn]
  have hmain := finite_selector_integral P A X hA hX hi s hs f 1
    (fun a _ => hf a) (fun a _ => hb a)
  have hdiag := finite_selector_integral P A X hA hX hi s hs
    (fun a _ => if a.1 = a.2 then (1 : ℝ) else 0) 1
    (by intros; exact measurable_const)
    (by intros; split_ifs <;> norm_num)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hdiag
  have hmean : (∫ ω, if (A ω).1 = (A ω).2 then (1 : ℝ) else 0 ∂P) =
      P.real {ω | source M.coordinate n u ω = source M.coordinate m v ω} := by
    have hmeas := source_eq_measurable P M n m u v
    simpa [Set.indicator_apply, A] using integral_indicator_one hmeas
  have hm (a : Label V × Label V) : (∫ ω, f a (X ω) ∂P) =
      if a.1 = a.2 then 1 else 0 := fixed_pair_sign_mean P M a.1 a.2
  simp_rw [hm] at hmain
  rw [← hdiag, hmean] at hmain
  simpa only [f, A, X, native_source] using hmain


private theorem fixed_four_sign_mean [DecidableEq V]
    (P : Measure Ω) (M : Model G P) (a b c d : Label V) :
    (∫ ω, (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
      (sgn (coin M.coordinate c ω) * sgn (coin M.coordinate d ω)) ∂P) =
      if (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) then 1 else 0 := by
  classical
  letI := M.probability
  have hs (l : Label V) (ω : Ω) : sgn (coin M.coordinate l ω) ^ 2 = 1 := by
    cases coin M.coordinate l ω <;> norm_num [sgn]
  have hcancel (l j k : Label V) :
      (∫ ω, (sgn (coin M.coordinate l ω) * sgn (coin M.coordinate j ω)) *
        (sgn (coin M.coordinate l ω) * sgn (coin M.coordinate k ω)) ∂P) =
        if j = k then 1 else 0 := by
    convert fixed_pair_sign_mean P M j k using 1
    congr 1
    funext ω
    calc
      _ = sgn (coin M.coordinate l ω) ^ 2 *
          (sgn (coin M.coordinate j ω) * sgn (coin M.coordinate k ω)) := by ring
      _ = _ := by rw [hs, one_mul]
  by_cases hab : a = b
  · subst b
    have he (ω : Ω) : (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate a ω)) *
        (sgn (coin M.coordinate c ω) * sgn (coin M.coordinate d ω)) =
        sgn (coin M.coordinate c ω) * sgn (coin M.coordinate d ω) := by
      rw [← pow_two, hs, one_mul]
    have hp : ((a = a ∧ c = d) ∨ (a = c ∧ a = d) ∨ (a = d ∧ a = c)) ↔ c = d := by
      constructor
      · rintro (h | h | h)
        · exact h.2
        · exact h.1.symm.trans h.2
        · exact h.2.symm.trans h.1
      · intro h; exact Or.inl ⟨rfl, h⟩
    simp only [eq_self_iff_true] at hp
    simp only [he, fixed_pair_sign_mean, hp]
  by_cases hcd : c = d
  · subst d
    have he (ω : Ω) : (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
        (sgn (coin M.coordinate c ω) * sgn (coin M.coordinate c ω)) =
        sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω) := by
      rw [← pow_two, hs, mul_one]
    have hp : ¬ ((a = b ∧ c = c) ∨ (a = c ∧ b = c) ∨ (a = c ∧ b = c)) := by
      rintro (h | h | h)
      · exact hab h.1
      · exact hab (h.1.trans h.2.symm)
      · exact hab (h.1.trans h.2.symm)
    simp only [eq_self_iff_true] at hp
    simp only [he, fixed_pair_sign_mean, if_neg hab, if_neg hp]
  by_cases hac : a = c
  · subst c
    simpa [hab, hcd] using hcancel a b d
  by_cases had : a = d
  · subst d
    have he (ω : Ω) : (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
        (sgn (coin M.coordinate c ω) * sgn (coin M.coordinate a ω)) =
        (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
        (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate c ω)) := by ring
    simpa [he, hab, hcd, hac] using hcancel a b c
  by_cases hbc : b = c
  · subst c
    have he (ω : Ω) : (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
        (sgn (coin M.coordinate b ω) * sgn (coin M.coordinate d ω)) =
        (sgn (coin M.coordinate b ω) * sgn (coin M.coordinate a ω)) *
        (sgn (coin M.coordinate b ω) * sgn (coin M.coordinate d ω)) := by ring
    simpa [he, hab, hcd, hac, had] using hcancel b a d
  by_cases hbd : b = d
  · subst d
    have he (ω : Ω) : (sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω)) *
        (sgn (coin M.coordinate c ω) * sgn (coin M.coordinate b ω)) =
        (sgn (coin M.coordinate b ω) * sgn (coin M.coordinate a ω)) *
        (sgn (coin M.coordinate b ω) * sgn (coin M.coordinate c ω)) := by ring
    simpa [he, hab, hcd, hac, had, hbc] using hcancel b a c
  have hm (l : Label V) : Measurable (coin M.coordinate l) := by
    cases l <;> exact M.measurable_coordinate _
  have hi := (coins_independent P M).indepFun_prodMk_prodMk hm a b c d hac had hbc hbd
  let g (p : Bool × Bool) := sgn p.1 * sgn p.2
  have hg : Measurable g := (measurable_of_finite sgn |>.comp measurable_fst).mul
    (measurable_of_finite sgn |>.comp measurable_snd)
  have he := hi.integral_fun_comp_mul_comp
    ((hm a).prodMk (hm b)).aemeasurable ((hm c).prodMk (hm d)).aemeasurable
    hg.aestronglyMeasurable hg.aestronglyMeasurable
  simpa [g, fixed_pair_sign_mean, hab, hcd, hac, had, hbc, hbd] using he

/-- The three possible even pairings are alternatives, not independent events. -/
def evenPairing {α : Type} (a : (α × α) × (α × α)) : Prop :=
  (a.1.1 = a.1.2 ∧ a.2.1 = a.2.2) ∨
  (a.1.1 = a.2.1 ∧ a.1.2 = a.2.2) ∨
  (a.1.1 = a.2.2 ∧ a.1.2 = a.2.1)

private theorem native_four_sign_mean (P : Measure Ω) (M : Model G P)
    (n₁ n₂ n₃ n₄ : ℕ) (u₁ u₂ u₃ u₄ : V) :
    (∫ ω, (sgn (nvm M.coordinate n₁ u₁ ω) * sgn (nvm M.coordinate n₂ u₂ ω)) *
      (sgn (nvm M.coordinate n₃ u₃ ω) * sgn (nvm M.coordinate n₄ u₄ ω)) ∂P) =
      P.real {ω | evenPairing
        ((source M.coordinate n₁ u₁ ω, source M.coordinate n₂ u₂ ω),
          (source M.coordinate n₃ u₃ ω, source M.coordinate n₄ u₄ ω))} := by
  classical
  letI := M.probability
  let A (ω : Ω) :=
    ((source M.coordinate n₁ u₁ ω, source M.coordinate n₂ u₂ ω),
      (source M.coordinate n₃ u₃ ω, source M.coordinate n₄ u₄ ω))
  let X (ω : Ω) (l : Label V) := coin M.coordinate l ω
  have hA : Measurable A :=
    ((source_measurable M.coordinate M.measurable_coordinate n₁ u₁).prodMk
      (source_measurable M.coordinate M.measurable_coordinate n₂ u₂)).prodMk
    ((source_measurable M.coordinate M.measurable_coordinate n₃ u₃).prodMk
      (source_measurable M.coordinate M.measurable_coordinate n₄ u₄))
  have hX : Measurable X := measurable_pi_iff.mpr (by
    intro l; cases l <;> exact M.measurable_coordinate _)
  have hi : IndepFun A X P := (sources_independent_coins P M).comp
    (((measurable_pi_apply (n₁,u₁)).prodMk (measurable_pi_apply (n₂,u₂))).prodMk
      ((measurable_pi_apply (n₃,u₃)).prodMk (measurable_pi_apply (n₄,u₄)))) measurable_id
  let s := ((possibleSources (G := G) n₁ u₁) ×ˢ (possibleSources (G := G) n₂ u₂)) ×ˢ
    ((possibleSources (G := G) n₃ u₃) ×ˢ (possibleSources (G := G) n₄ u₄))
  have hs (ω : Ω) : A ω ∈ s := Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨source_mem_possible M.coordinate n₁ u₁ ω,
        source_mem_possible M.coordinate n₂ u₂ ω⟩,
      Finset.mem_product.mpr ⟨source_mem_possible M.coordinate n₃ u₃ ω,
        source_mem_possible M.coordinate n₄ u₄ ω⟩⟩
  let f (a : (Label V × Label V) × (Label V × Label V)) (x : Label V → Bool) :=
    (sgn (x a.1.1) * sgn (x a.1.2)) * (sgn (x a.2.1) * sgn (x a.2.2))
  have hf (a : (Label V × Label V) × (Label V × Label V)) : Measurable (f a) :=
    (((measurable_of_finite sgn).comp (measurable_pi_apply a.1.1)).mul
      ((measurable_of_finite sgn).comp (measurable_pi_apply a.1.2))).mul
    (((measurable_of_finite sgn).comp (measurable_pi_apply a.2.1)).mul
      ((measurable_of_finite sgn).comp (measurable_pi_apply a.2.2)))
  have hb (a : (Label V × Label V) × (Label V × Label V)) (x : Label V → Bool) :
      ‖f a x‖ ≤ 1 := by
    dsimp only [f]
    cases h₁ : x a.1.1 <;> cases h₂ : x a.1.2 <;>
      cases h₃ : x a.2.1 <;> cases h₄ : x a.2.2 <;> norm_num [h₁,h₂,h₃,h₄,sgn]
  have hmain := finite_selector_integral P A X hA hX hi s hs f 1
    (fun a _ => hf a) (fun a _ => hb a)
  have hdiag := finite_selector_integral P A X hA hX hi s hs
    (fun a _ => if evenPairing a then (1 : ℝ) else 0) 1
    (by intros; exact measurable_const)
    (by intros; split_ifs <;> norm_num)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hdiag
  have hmeas : MeasurableSet {ω | evenPairing (A ω)} := by
    have heq : {ω | evenPairing (A ω)} =
        ⋃ a : {a // a ∈ s ∧ evenPairing a}, A ⁻¹' {a.val} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨⟨A ω, hs ω, h⟩, rfl⟩
      · rintro ⟨a, ha⟩
        exact ha ▸ a.property.2
    rw [heq]
    haveI : Finite {a // a ∈ s ∧ evenPairing a} :=
      Finite.of_injective (fun a => (⟨a.val, a.property.1⟩ : ↑s))
        (by intro a b h; exact Subtype.ext (congrArg (fun x : ↑s => x.val) h))
    exact MeasurableSet.iUnion (fun a => hA (measurableSet_singleton a.val))
  have hmean : (∫ ω, if evenPairing (A ω) then (1 : ℝ) else 0 ∂P) =
      P.real {ω | evenPairing (A ω)} := by
    simpa [Set.indicator_apply] using integral_indicator_one hmeas
  have hm (a : (Label V × Label V) × (Label V × Label V)) :
      (∫ ω, f a (X ω) ∂P) = if evenPairing a then 1 else 0 := by
    have hh := fixed_four_sign_mean P M a.1.1 a.1.2 a.2.1 a.2.2
    by_cases hp : evenPairing a
    · dsimp only [evenPairing] at hp
      simpa [f, X, evenPairing, hp] using hh
    · dsimp only [evenPairing] at hp
      simpa [f, X, evenPairing, hp] using hh
  simp_rw [hm] at hmain
  rw [← hdiag, hmean] at hmain
  simpa only [f, A, X, native_source] using hmain

end D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources


open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources

open RepetitionVarianceLinear
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

variable {V Ω : Type} {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace Ω]


private def Z {P : Measure Ω} (M : Model G P) (u : V) (d i : ℕ) (ω : Ω) : ℝ :=
  sgn (nvm M.coordinate i u ω) * sgn (nvm M.coordinate (i+d) u ω)

private noncomputable def C {P : Measure Ω} (M : Model G P) (u : V) (d i : ℕ) (ω : Ω) : ℝ :=
  by
  classical
  exact if source M.coordinate i u ω = source M.coordinate (i+d) u ω then 1 else 0

private theorem Z_memLp (P : Measure Ω) (M : Model G P) (u : V) (d i : ℕ) :
    MemLp (Z M u d i) 2 P := by
  letI := M.probability
  apply MemLp.of_bound
    (((measurable_of_finite sgn).comp (nvm_measurable M.coordinate M.measurable_coordinate i u)).mul
      ((measurable_of_finite sgn).comp
        (nvm_measurable M.coordinate M.measurable_coordinate (i+d) u))).aestronglyMeasurable 1
  apply Eventually.of_forall
  intro ω
  cases h₁ : nvm M.coordinate i u ω <;> cases h₂ : nvm M.coordinate (i+d) u ω <;>
    norm_num [h₁,h₂,sgn]

private theorem C_memLp (P : Measure Ω) (M : Model G P) (u : V) (d i : ℕ) :
    MemLp (C M u d i) 2 P := by
  classical
  letI := M.probability
  apply MemLp.of_bound
    (Measurable.ite (source_eq_measurable P M i (i+d) u u)
      measurable_const measurable_const).aestronglyMeasurable 1
  apply Eventually.of_forall
  intro ω
  split_ifs <;> norm_num

private theorem C_mean (P : Measure Ω) (M : Model G P) (u : V) (d i : ℕ) :
    (∫ ω, C M u d i ω ∂P) =
      P.real {ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω} := by
  classical
  simpa [C, Set.indicator_apply] using
    integral_indicator_one (source_eq_measurable P M i (i+d) u u)

private theorem covariance_domination (P : Measure Ω) (M : Model G P)
    (u : V) (d i j : ℕ) :
    cov[C M u d i, C M u d j; P] ≤ cov[Z M u d i, Z M u d j; P] := by
  classical
  letI := M.probability
  rw [covariance_eq_sub (C_memLp P M u d i) (C_memLp P M u d j),
    covariance_eq_sub (Z_memLp P M u d i) (Z_memLp P M u d j)]
  have hmean (k : ℕ) : (∫ ω, Z M u d k ω ∂P) = (∫ ω, C M u d k ω ∂P) := by
    rw [C_mean]
    exact native_pair_sign_mean P M k (k+d) u u
  simp only [hmean]
  apply sub_le_sub_right
  have hcc : (∫ ω, (C M u d i * C M u d j) ω ∂P) =
      P.real ({ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω} ∩
        {ω | source M.coordinate j u ω = source M.coordinate (j+d) u ω}) := by
    have he (ω : Ω) : (C M u d i * C M u d j) ω =
        ({ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω} ∩
          {ω | source M.coordinate j u ω = source M.coordinate (j+d) u ω}).indicator
            (fun _ => (1 : ℝ)) ω := by
      simp only [Pi.mul_apply, C, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    simp_rw [he]
    exact integral_indicator_one ((source_eq_measurable P M i (i+d) u u).inter
      (source_eq_measurable P M j (j+d) u u))
  rw [hcc]
  change _ ≤ ∫ ω, (sgn (nvm M.coordinate i u ω) * sgn (nvm M.coordinate (i+d) u ω)) *
    (sgn (nvm M.coordinate j u ω) * sgn (nvm M.coordinate (j+d) u ω)) ∂P
  rw [native_four_sign_mean]
  exact measureReal_mono (fun ω h => Or.inl ⟨h.1,h.2⟩) (measure_ne_top _ _)

private theorem diagonal_difference (P : Measure Ω) (M : Model G P)
    (u : V) (d i : ℕ) :
    cov[Z M u d i, Z M u d i; P] - cov[C M u d i, C M u d i; P] =
      1 - P.real {ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω} := by
  classical
  letI := M.probability
  rw [covariance_self (Z_memLp P M u d i).aemeasurable,
    covariance_self (C_memLp P M u d i).aemeasurable,
    variance_eq_sub (Z_memLp P M u d i), variance_eq_sub (C_memLp P M u d i)]
  have hz (ω : Ω) : (Z M u d i ^ 2) ω = 1 := by
    dsimp only [Pi.pow_apply, Z]
    cases h₁ : nvm M.coordinate i u ω <;> cases h₂ : nvm M.coordinate (i+d) u ω <;>
      norm_num [h₁,h₂,sgn]
  have hc (ω : Ω) : (C M u d i ^ 2) ω = C M u d i ω := by
    dsimp only [Pi.pow_apply, C]
    split_ifs <;> norm_num
  simp_rw [hz, hc]
  rw [integral_const]
  have hm := native_pair_sign_mean P M i (i+d) u u
  change (∫ ω, Z M u d i ω ∂P) = _ at hm
  rw [hm, C_mean]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- A finite-time lower bound with the actual collision probabilities retained. -/
private theorem native_variance_lower (P : Measure Ω) (M : Model G P) (u : V) (d t : ℕ) :
    (1 / 4 : ℝ) * ∑ i ∈ Finset.Icc 1 t,
      (1 - P.real {ω | source M.coordinate i u ω = source M.coordinate (i+d) u ω}) ≤
      variance (W M.coordinate u d t) P := by
  classical
  letI := M.probability
  let s := Finset.Icc 1 t
  have hdiff : (∑ i ∈ s, (1 - P.real {ω | source M.coordinate i u ω =
      source M.coordinate (i+d) u ω})) ≤
      variance (fun ω => ∑ i ∈ s, Z M u d i ω) P -
      variance (fun ω => ∑ i ∈ s, C M u d i ω) P := by
    rw [variance_fun_sum' (fun i _ => Z_memLp P M u d i),
      variance_fun_sum' (fun i _ => C_memLp P M u d i), ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [← Finset.sum_sub_distrib, ← diagonal_difference P M u d i]
    exact Finset.single_le_sum (fun j _ => sub_nonneg.mpr (covariance_domination P M u d i j)) hi
  have hbound : (∑ i ∈ s, (1 - P.real {ω | source M.coordinate i u ω =
      source M.coordinate (i+d) u ω})) ≤ variance (fun ω => ∑ i ∈ s, Z M u d i ω) P :=
    hdiff.trans (sub_le_self _ (variance_nonneg _ _))
  have hw : W M.coordinate u d t = fun ω =>
      (1/2 : ℝ) * (∑ i ∈ s, Z M u d i ω) + (s.card : ℝ) / 2 := by
    funext ω
    dsimp only [W]
    rw [Finset.mul_sum]
    have he (i : ℕ) : (if nvm M.coordinate i u ω = nvm M.coordinate (i+d) u ω then
        (1 : ℝ) else 0) = (1/2 : ℝ) * Z M u d i ω + 1/2 := by
      dsimp only [Z]
      cases h₁ : nvm M.coordinate i u ω <;> cases h₂ : nvm M.coordinate (i+d) u ω <;>
        norm_num [h₁,h₂,sgn]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [s, div_eq_mul_inv]
  rw [hw, variance_add_const, variance_const_mul]
  · simpa only [s, show (1/2 : ℝ)^2 = 1/4 by norm_num] using
      mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ 1/4 by norm_num)
  · simpa only [Finset.sum_apply] using
      ((memLp_finsetSum' s (fun i _ => Z_memLp P M u d i)).const_mul
        (1/2 : ℝ)).aestronglyMeasurable


/-- The lower endpoint is independent of the graph degree and observation spacing. -/
theorem uniform_variance_lower (P : Measure Ω) (M : Model G P) (u : V) (d t : ℕ) :
    (t : ℝ) / 4 * (1 - (1 - (M.ε : ℝ)) ^ d) ≤
      variance (W M.coordinate u d t) P := by
  letI := M.probability
  have hcol (i : ℕ) : P.real {ω | source M.coordinate i u ω =
      source M.coordinate (i+d) u ω} ≤ (1 - (M.ε : ℝ)) ^ d := by
    have hh := ENNReal.toReal_mono
      (show (unitInterval.toNNReal (unitInterval.symm M.ε) : ℝ≥0∞) ^ d ≠ ⊤ by finiteness)
      (collision_probability_le P M i d u)
    simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.coe_toReal,
      unitInterval.coe_toNNReal, unitInterval.coe_symm_eq] using hh
  have hh := Finset.sum_le_sum (s := Finset.Icc 1 t)
    (fun i _ => sub_le_sub_left (hcol i) 1)
  have hc : (Finset.Icc 1 t).card = t := by simp
  have hsum : (t : ℝ) * (1 - (1 - (M.ε : ℝ)) ^ d) ≤
      ∑ i ∈ Finset.Icc 1 t, (1 - P.real {ω | source M.coordinate i u ω =
        source M.coordinate (i+d) u ω}) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hc] using hh
  have hscaled := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1/4 by norm_num)
  calc
    _ = (1/4 : ℝ) * ((t : ℝ) * (1 - (1 - (M.ε : ℝ)) ^ d)) := by ring
    _ ≤ _ := hscaled
    _ ≤ _ := native_variance_lower P M u d t

end D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
