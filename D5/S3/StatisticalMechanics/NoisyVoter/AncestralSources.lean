/- GID: D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/AncestralSources
   mirror-E: none
   anchors: []
   utility: none
   digest: Synchronous noisy voter opinions retain their actual independent source labels. -/

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

theorem source_birth_le (x : (i : Coord V) → Ω → Value G i) :
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

theorem survives_iff_old_source (x : (i : Coord V) → Ω → Value G i) (i : ℕ) :
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

theorem collision_requires_survival (x : (i : Coord V) → Ω → Value G i)
    (i d : ℕ) (u : V) (ω : Ω)
    (h : source x i u ω = source x (i+d) u ω) : survives x i d u ω = true := by
  apply (survives_iff_old_source x i d u ω).2
  rw [← h]
  exact source_birth_le x i u ω

instance labelMeasurable : MeasurableSpace (Label V) := ⊤

instance labelMeasurableSingleton : MeasurableSingletonClass (Label V) := ⟨fun _ => trivial⟩

theorem source_measurable [G.LocallyFinite] [MeasurableSpace Ω]
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

theorem source_past {Ω' : Type}
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

theorem source_mem_possible [G.LocallyFinite]
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

theorem survives_measurable [G.LocallyFinite] [MeasurableSpace Ω]
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

theorem survival_probability [G.LocallyFinite] [MeasurableSpace Ω]
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
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, A, survives, R, J]
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

theorem collision_probability_le [G.LocallyFinite] [MeasurableSpace Ω]
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

theorem sources_independent_coins [G.LocallyFinite] [MeasurableSpace Ω]
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

theorem coins_independent [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) : iIndepFun (coin M.coordinate) P := by
  have h := (M.independent.precomp labelCoordinate_injective).comp
    (fun l => readCoin (G := G) l) (by intro l; cases l <;> exact measurable_id)
  convert h using 1
  funext l ω
  cases l <;> rfl

theorem coin_hasLaw [G.LocallyFinite] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (l : Label V) :
    HasLaw (coin M.coordinate l)
      (bernoulliMeasure true false (⟨1/2, by norm_num, by norm_num⟩ : unitInterval)) P := by
  cases l with
  | inl v => exact M.laws (.initial v)
  | inr p => exact M.laws (.fresh p.1.val p.2)

end D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
