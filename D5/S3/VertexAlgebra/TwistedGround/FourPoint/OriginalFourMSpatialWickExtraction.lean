/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spatial Taylor extraction on disjoint occurrence supports. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialTaylor
import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution

/-! Spatial Taylor extraction factors through products whose coordinate
supports lie on opposite sides of a partition of the occurrences. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction

open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMSpatialWick (spatialCoefficient)
open AffineWickConvolution (partitions)
open AffineOccurrenceWick (wick)
open scoped BigOperators Topology
open Filter
open private take take_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialTaylor

variable {X : Type*} [DecidableEq X]

/-- Agreement on the selected coordinates suffices to determine a factor. -/
def DependsOn (s : Set X) (f : (X → ℂ) → ℂ) : Prop :=
  ∀ ⦃u v⦄, Set.EqOn u v s → f u = f v

private theorem DependsOn.afterTake {s : Set X} {f : (X → ℂ) → ℂ}
    (hf : DependsOn s f) (n : X → ℕ) (a : X) : DependsOn s (take n a f) := by
  intro u v h
  unfold take
  congr 1
  funext t
  apply hf
  intro i hi
  by_cases he : i = a
  · subst i
    simp
  · simpa only [Function.update_of_ne he] using h hi

private theorem take_mul_right (n : X → ℕ) (a : X) {s : Set X}
    (f g : (X → ℂ) → ℂ) (hg : DependsOn s g) (ha : a ∉ s) :
    take n a (fun u => f u * g u) = fun u => take n a f u * g u := by
  funext u
  have he (t : ℂ) : g (Function.update u a t) = g u :=
    hg (u := Function.update u a t) (v := u) (fun i hi => by
      have hn : i ≠ a := fun h => ha (h ▸ hi)
      exact Function.update_of_ne hn _ _)
  simp only [take, he, coefficient, iteratedDeriv_mul_const_field, div_mul_eq_mul_div]

private theorem take_mul_left (n : X → ℕ) (a : X) {s : Set X}
    (f g : (X → ℂ) → ℂ) (hf : DependsOn s f) (ha : a ∉ s) :
    take n a (fun u => f u * g u) = fun u => f u * take n a g u := by
  simpa only [mul_comm] using take_mul_right n a g f hf ha

/-- The ordinary Taylor coefficient of a product on two disjoint sets of
coordinates is the product of the ordered Taylor coefficients of each factor. -/
theorem spatialCoefficient_mul_filter (n : X → ℕ) (l : List X) (p : X → Bool)
    (f g : (X → ℂ) → ℂ) (hf : DependsOn {a | p a = true} f)
    (hg : DependsOn {a | p a = false} g) (u : X → ℂ) :
    spatialCoefficient n l (fun v => f v * g v) u =
      spatialCoefficient n (l.filter p) f u *
        spatialCoefficient n (l.filter fun a => !p a) g u := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    cases he : p a
    · simp only [spatialCoefficient, List.filter_cons, he, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true]
      rw [take_mul_left n a f g hf (by simp [he])]
      exact ih f (take n a g) hf (hg.afterTake n a)
    · simp only [spatialCoefficient, List.filter_cons, he, Bool.not_true,
        Bool.false_eq_true, ite_false, ite_true]
      rw [take_mul_right n a f g hg (by simp [he])]
      exact ih (take n a f) g (hf.afterTake n a) hg

/-- A position partition of a distinct occurrence word is obtained by
filtering it by membership in the first subword. -/
theorem partition_eq_filters (l : List X) (p : List X × List X)
    (hl : l.Nodup) (hp : p ∈ partitions l) :
    l.filter (fun a => decide (a ∈ p.1)) = p.1 ∧
      l.filter (fun a => !(decide (a ∈ p.1))) = p.2 := by
  induction l generalizing p with
  | nil =>
    simp [partitions] at hp
    subst p
    simp
  | cons a l ih =>
    have ⟨ha, hl⟩ := List.nodup_cons.mp hl
    simp only [partitions, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h₁, h₂⟩ := ih q hl hq
      have he : l.filter (fun x => decide (x ∈ a :: q.1)) =
          l.filter (fun x => decide (x ∈ q.1)) := by
        apply List.filter_congr
        intro x hx
        have hn : x ≠ a := fun h => ha (h ▸ hx)
        simp [hn]
      have he' : l.filter (fun x => !(decide (x ∈ a :: q.1))) =
          l.filter (fun x => !(decide (x ∈ q.1))) := by
        apply List.filter_congr
        intro x hx
        have hn : x ≠ a := fun h => ha (h ▸ hx)
        simp [hn]
      simp only [List.filter_cons, List.mem_cons_self, decide_true, Bool.not_true,
        ite_true, Bool.false_eq_true, ite_false, he, he', h₁, h₂, and_self]
    · obtain ⟨h₁, h₂⟩ := ih q hl hq
      have ha' : a ∉ q.1 := by
        rw [← h₁]
        exact fun h => ha (List.mem_of_mem_filter h)
      simp [ha', h₁, h₂]

/-- Spatial extraction on an ordered partition acts on each subword
independently, including empty subwords and mode zero. -/
theorem spatialCoefficient_mul_partition (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (p : List X × List X) (hp : p ∈ partitions l) (f g : (X → ℂ) → ℂ)
    (hf : DependsOn {a | a ∈ p.1} f) (hg : DependsOn {a | a ∈ p.2} g)
    (u : X → ℂ) :
    spatialCoefficient n l (fun v => f v * g v) u =
      spatialCoefficient n p.1 f u * spatialCoefficient n p.2 g u := by
  obtain ⟨h₁, h₂⟩ := partition_eq_filters l p hl hp
  have he : ∀ a ∈ p.2, a ∉ p.1 := by
    intro a ha
    rw [← h₂, List.mem_filter] at ha
    simpa using ha.2
  rw [spatialCoefficient_mul_filter n l (fun a => decide (a ∈ p.1)) f g
    (fun {u v} h => hf (u := u) (v := v) (fun a ha => h (by simpa using ha)))
    (fun {u v} h => hg (u := u) (v := v) (fun a ha => h (by simpa using he a ha))), h₁, h₂]

omit [DecidableEq X] in
/-- A Wick evaluation depends only on the coordinates of the occurrences
that enter its singleton and pair branches. -/
theorem wick_dependsOn (A : X → X → ℂ → ℂ → ℂ) (μ : X → ℂ → ℂ) (l : List X) :
    DependsOn {a | a ∈ l}
      (fun u => wick (Matrix.of fun i j => A i j (u i) (u j)) (fun i => μ i (u i)) l) := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    unfold DependsOn at ih ⊢
    intro u v huv
    cases l with
    | nil => simp [wick]
    | cons a l =>
      have ha := huv (List.mem_cons_self (a := a) (l := l))
      have ht := ih l (Nat.lt_succ_self _) (u := u) (v := v)
        (fun i hi => huv (List.mem_cons_of_mem _ hi))
      simp only [wick, Matrix.of_apply]
      dsimp only at ht
      rw [ht, ha]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hj := huv (List.mem_cons_of_mem a (List.get_mem l j))
      have he := ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
        (u := u) (v := v)
        (fun i hi => huv (List.mem_cons_of_mem a ((List.eraseIdx_sublist ..).subset hi)))
      dsimp only at he
      rw [he, hj]

variable [Fintype X]

private theorem slice_analytic {f : (X → ℂ) → ℂ} {u : X → ℂ} (a : X)
    (hf : AnalyticAt ℂ f (Function.update u a 0)) :
    AnalyticAt ℂ (fun t => f (Function.update u a t)) 0 := by
  refine hf.comp ?_
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases he : j = a
  · subst j
    change AnalyticAt ℂ (fun t : ℂ => Function.update u a t a) 0
    rw [show (fun t : ℂ => Function.update u a t a) = id from
      funext fun t => Function.update_self a t u]
    exact analyticAt_id
  · simpa only [Function.update_of_ne he] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => u j) 0)

private theorem take_add (n : X → ℕ) (a : X) {f g : (X → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    take n a (fun u => f u + g u) =ᶠ[𝓝 0] fun u => take n a f u + take n a g u := by
  have hc : Continuous (fun u : X → ℂ => Function.update u a 0) := by
    apply continuous_pi
    intro i
    by_cases he : i = a
    · subst i
      simp only [Function.update_self]
      exact continuous_const
    · simpa only [Function.update_of_ne he] using continuous_apply i
  have ht := hc.continuousAt.tendsto (x := (0 : X → ℂ))
  have hzero : Function.update (0 : X → ℂ) a 0 = 0 := by simp
  rw [hzero] at ht
  filter_upwards [ht.eventually hf.eventually_analyticAt, ht.eventually hg.eventually_analyticAt]
    with u hfu hgu
  simp only [take, coefficient, ← add_div]
  exact congrArg (fun z : ℂ => z / ((n a).factorial : ℂ))
    (iteratedDeriv_add (slice_analytic a hfu).contDiffAt (slice_analytic a hgu).contDiffAt)

/-- Finite spatial coefficient extraction is additive on analytic germs. -/
theorem spatialCoefficient_add (n : X → ℕ) (l : List X) {f g : (X → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    spatialCoefficient n l (fun u => f u + g u) 0 =
      spatialCoefficient n l f 0 + spatialCoefficient n l g 0 := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    simp only [spatialCoefficient]
    rw [(OriginalFourMSpatialWick.spatialCoefficient_congr n l (take_add n a hf hg)).eq_of_nhds]
    exact ih (take_analytic n a _ hf) (take_analytic n a _ hg)

omit [DecidableEq X] in
/-- The Wick recursion preserves analyticity of the individual spatial
singleton and pair germs. -/
theorem wick_analytic (A : (X → ℂ) → Matrix X X ℂ) (μ : (X → ℂ) → X → ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun u => A u i j) 0)
    (hμ : ∀ i, AnalyticAt ℂ (fun u => μ u i) 0) (l : List X) :
    AnalyticAt ℂ (fun u => wick (A u) (μ u) l) 0 := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simpa only [wick] using (analyticAt_const :
        AnalyticAt ℂ (fun _ : X → ℂ => (1 : ℂ)) 0)
    | cons a l =>
      simp only [wick]
      apply AnalyticAt.add ((hμ a).mul (ih l (Nat.lt_succ_self _)))
      apply Finset.analyticAt_fun_sum
      intro j _
      exact (hA a (l.get j)).mul
        (ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..)))

omit [DecidableEq X] [Fintype X] in
private theorem no_left_mem (l : List X) : ([], l) ∈ partitions l := by
  induction l with
  | nil => simp [partitions]
  | cons a l ih =>
    rw [partitions, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨([], l), ih, rfl⟩)

omit [DecidableEq X] [Fintype X] in
private theorem one_left_mem (l : List X) (j : Fin l.length) :
    ([l.get j], l.eraseIdx j) ∈ partitions l := by
  induction l with
  | nil => exact Fin.elim0 j
  | cons a l ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [partitions, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨([], l), no_left_mem l, rfl⟩)
    · simp only [Fin.val_succ, List.get_cons_succ', List.eraseIdx_cons_succ,
        partitions, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨_, ih k, rfl⟩)

omit [Fintype X] in
private theorem spatialCoefficient_zero (n : X → ℕ) (l : List X) :
    spatialCoefficient n l (fun _ => 0) 0 = 0 := by
  simpa only [zero_mul] using
    congrFun (OriginalFourMSpatialWick.spatialCoefficient_const_mul n l 0 (fun _ => 1)) 0

/-- Finite spatial coefficient extraction commutes with a list sum of analytic
germs, keeping any repeated summands. -/
theorem spatialCoefficient_list_sum {J : Type*} (n : X → ℕ) (l : List X)
    (terms : List J) (f : J → (X → ℂ) → ℂ)
    (hf : ∀ j ∈ terms, AnalyticAt ℂ (f j) 0) :
    spatialCoefficient n l (fun u => (terms.map fun j => f j u).sum) 0 =
      (terms.map fun j => spatialCoefficient n l (f j) 0).sum := by
  have ha (s : List J) (hs : ∀ j ∈ s, AnalyticAt ℂ (f j) 0) :
      AnalyticAt ℂ (fun u => (s.map fun j => f j u).sum) 0 := by
    induction s with
    | nil => exact analyticAt_const
    | cons j s ih =>
      exact (hs j List.mem_cons_self).add (ih fun k hk => hs k (List.mem_cons_of_mem _ hk))
  induction terms with
  | nil => exact spatialCoefficient_zero n l
  | cons j terms ih =>
    have ht (k : J) (hk : k ∈ terms) := hf k (List.mem_cons_of_mem _ hk)
    simp only [List.map_cons, List.sum_cons]
    rw [spatialCoefficient_add n l (hf j List.mem_cons_self) (ha terms ht), ih ht]

private theorem spatialCoefficient_sum {J : Type*} (n : X → ℕ) (l : List X)
    (s : Finset J) (f : J → (X → ℂ) → ℂ) (hf : ∀ j ∈ s, AnalyticAt ℂ (f j) 0) :
    spatialCoefficient n l (fun u => ∑ j ∈ s, f j u) 0 =
      ∑ j ∈ s, spatialCoefficient n l (f j) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using spatialCoefficient_zero n l
  | insert j s hj ih =>
    have ht k hk := hf k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [spatialCoefficient_add n l (hf j (Finset.mem_insert_self ..))
      (Finset.analyticAt_fun_sum s ht), ih ht]

/-- Spatial extraction through Wick's recurrence replaces each singleton
and pair by its own ordinary Taylor coefficients. The pair follows the
order of its two occurrences in the original word. -/
theorem spatialCoefficient_wick (A : X → X → ℂ → ℂ → ℂ) (μ : X → ℂ → ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun u : X → ℂ => A i j (u i) (u j)) 0)
    (hμ : ∀ i, AnalyticAt ℂ (fun u : X → ℂ => μ i (u i)) 0)
    (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    spatialCoefficient n l (fun u => wick (Matrix.of fun i j => A i j (u i) (u j))
      (fun i => μ i (u i)) l) 0 =
      wick (Matrix.of fun i j => coefficient (n j) (fun v => coefficient (n i) (fun u => A i j u v)))
        (fun i => coefficient (n i) (μ i)) l := by
  let F (s : List X) := fun u : X → ℂ =>
    wick (Matrix.of fun i j => A i j (u i) (u j)) (fun i => μ i (u i)) s
  have hF (s : List X) : AnalyticAt ℂ (F s) 0 := wick_analytic _ _ hA hμ s
  change spatialCoefficient n l (F l) 0 = _
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [F, spatialCoefficient, wick]
    | cons a l =>
      let B (j : Fin l.length) := fun u : X → ℂ =>
        A a (l.get j) (u a) (u (l.get j)) * F (l.eraseIdx j) u
      have hB (j : Fin l.length) : AnalyticAt ℂ (B j) 0 :=
        (hA a (l.get j)).mul (hF (l.eraseIdx j))
      have hN := List.nodup_cons.mp hl
      have he : F (a :: l) = fun u => μ a (u a) * F l u + ∑ j, B j u := by
        funext u
        simp only [F, wick, Matrix.of_apply, B]
      rw [he, spatialCoefficient_add n (a :: l)
        (f := fun u => μ a (u a) * F l u)
        (g := fun u => ∑ j, B j u) ((hμ a).mul (hF l))
        (Finset.analyticAt_fun_sum Finset.univ fun j _ => hB j),
        spatialCoefficient_sum n (a :: l) Finset.univ B (fun j _ => hB j), wick]
      simp only [Matrix.of_apply]
      congr 1
      · have hp : ([a], l) ∈ partitions (a :: l) := by
          rw [partitions, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨([], l), no_left_mem l, rfl⟩)
        have hd : DependsOn {i | i ∈ [a]} (fun u : X → ℂ => μ a (u a)) :=
          fun {_ _} h => congrArg (μ a) (h (show a ∈ [a] from by simp))
        rw [spatialCoefficient_mul_partition n _ hl ([a], l) hp _ _ hd
          (wick_dependsOn A μ l), ih l (Nat.lt_succ_self _) hN.2]
        simp [spatialCoefficient, take]
      · apply Finset.sum_congr rfl
        intro j _
        let b := l.get j
        have hb : b ≠ a := fun h => hN.1 (h ▸ List.get_mem l j)
        have hp : ([a, b], l.eraseIdx j) ∈ partitions (a :: l) := by
          rw [partitions, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨_, one_left_mem l j, rfl⟩)
        have hd : DependsOn {i | i ∈ [a, b]} (fun u : X → ℂ => A a b (u a) (u b)) :=
          fun {_ _} h => congrArg₂ (A a b)
            (h (show a ∈ [a, b] from by simp)) (h (show b ∈ [a, b] from by simp))
        change spatialCoefficient n (a :: l) (fun u => A a b (u a) (u b) *
          F (l.eraseIdx j) u) 0 = _
        rw [spatialCoefficient_mul_partition n _ hl ([a, b], l.eraseIdx j) hp _ _ hd
          (wick_dependsOn A μ _), ih (l.eraseIdx j)
            (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
            ((List.eraseIdx_sublist ..).nodup hN.2)]
        simp only [spatialCoefficient, take, Function.update_self,
          Function.update_of_ne hb]
        rfl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
