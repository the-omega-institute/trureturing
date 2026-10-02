/- GID: D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope
   mirror-E: none(waiver:finite-tree-envelope)
   anchors: []
   utility: none
   digest: The original five-point Bellman iteration is the whole closed-domain finite barycentric-tree value. -/

import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open scoped BigOperators
open Set
namespace D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open FiniteLocalLatitudeGeometry
set_option autoImplicit false
set_option maxRecDepth 4000

abbrev Ball := Metric.closedBall (0 : Bloch) 1
abbrev State := Ball × Ball

def active (actor : Bool) (z : State) : Ball := if actor then z.2 else z.1
def passive (actor : Bool) (z : State) : Ball := if actor then z.1 else z.2
def place (actor : Bool) (x b : Ball) : State := if actor then (b,x) else (x,b)

/-- A complete finite split includes zero weights and all boundary points. -/
structure Split (n : ℕ) (a : Ball) where
  w : Fin n → ℝ
  x : Fin n → Ball
  nonneg : ∀ i, 0 ≤ w i
  total : ∑ i, w i = 1
  mean : ∑ i, w i • (x i : Bloch) = (a : Bloch)

/-- Every node changes one coordinate; stopping has no required split. -/
inductive Tree : State → Type
  | stop (z : State) : Tree z
  | node (actor : Bool) (z : State) (n : ℕ) (s : Split n (active actor z))
      (next : ∀ i, Tree (place actor (s.x i) (passive actor z))) : Tree z

def Tree.reward (u : State → ℝ) {z : State} : Tree z → ℝ
  | .stop z => u z
  | .node _ _ _ s next => ∑ i, s.w i * (next i).reward u

def Tree.depth {z : State} : Tree z → ℕ
  | .stop _ => 0
  | .node _ _ _ _ next => 1 + Finset.univ.sup (fun i => (next i).depth)

def Tree.Leaves {z : State} : Tree z → Type
  | .stop _ => Unit
  | .node _ _ _ _ next => (i : _) × (next i).Leaves

noncomputable instance Tree.fintypeLeaves {z : State} (T : Tree z) : Fintype T.Leaves := by
  induction T with
  | stop => exact inferInstanceAs (Fintype Unit)
  | node _ _ _ _ _ ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((i : _) × _))

def Tree.endpoint {z : State} (T : Tree z) : T.Leaves → State :=
  match T with
  | .stop z => fun _ => z
  | .node _ _ _ _ next => fun l => (next l.1).endpoint l.2

def Tree.expect {z : State} (T : Tree z) (F : T.Leaves → ℝ) : ℝ :=
  match T with
  | .stop _ => F ()
  | .node _ _ _ s next => ∑ i, s.w i * (next i).expect (fun l => F ⟨i,l⟩)

/-- Inductive complete cuts are prefix-free and include every terminal path. -/
inductive Tree.Cut : {z : State} → Tree z → Type
  | here {z : State} (T : Tree z) : Cut T
  | descend (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z))
      (next : ∀ i, Tree (place actor (s.x i) (passive actor z)))
      (cuts : ∀ i, Cut (next i)) : Cut (.node actor z m s next)

def Tree.Cut.Nodes {z : State} {T : Tree z} : T.Cut → Type
  | .here _ => Unit
  | .descend _ _ _ _ _ cuts => (i : _) × (cuts i).Nodes

noncomputable instance Tree.Cut.fintypeNodes {z : State} {T : Tree z} (cut : T.Cut) :
    Fintype cut.Nodes := by
  induction cut with
  | here => exact inferInstanceAs (Fintype Unit)
  | descend _ _ _ _ _ _ ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((i : _) × _))

def Tree.Cut.branch {z : State} {T : Tree z} (cut : T.Cut) : cut.Nodes → (z : State) × Tree z :=
  match cut with
  | .here T => fun _ => ⟨z,T⟩
  | .descend _ _ _ _ _ cuts => fun v => (cuts v.1).branch v.2

def Tree.Cut.mass {z : State} {T : Tree z} (cut : T.Cut) : cut.Nodes → ℝ :=
  match cut with
  | .here _ => fun _ => 1
  | .descend _ _ _ s _ cuts => fun v => s.w v.1 * (cuts v.1).mass v.2

def d (z : State) : ℝ := defect (z.1 : Bloch) (z.2 : Bloch)

def terminal (r : ℝ) (z : State) : ℝ :=
  (K_s r).indicator (fun _ => h r) ((z.1 : Bloch),(z.2 : Bloch))

/-- The numerical five-point formula. Its source operator domain is `Admissible`. -/
def fiveValue (actor : Bool) (u : State → ℝ) (z : State) : ℝ :=
  sSup {t | ∃ s : Split 5 (active actor z),
    t = ∑ i, s.w i * u (place actor (s.x i) (passive actor z))}

def Admissible (r : ℝ) (u : State → ℝ) : Prop :=
  UpperSemicontinuous u ∧ ∀ z, 0 ≤ u z ∧ u z ≤ h r

def C (r : ℝ) (actor : Bool) (u : State → ℝ) (_ : Admissible r u) : State → ℝ :=
  fiveValue actor u

def V (r : ℝ) : ℕ → State → ℝ
  | 0 => terminal r
  | n+1 => fun z => max (fiveValue false (V r n) z) (fiveValue true (V r n) z)

def VInfinity (r : ℝ) (z : State) : ℝ := sSup (Set.range (fun n => V r n z))
def treeValue (r : ℝ) (z : State) : ℝ :=
  sSup {t | ∃ T : Tree z, t = T.reward (terminal r)}

/-- Finite Jensen inequalities in each coordinate, on the entire closed ball. -/
def SeparatelyConcave (u : State → ℝ) : Prop :=
  ∀ (actor : Bool) (z : State) (n : ℕ) (s : Split n (active actor z)),
    (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ≤ u z

def fSEP (r : ℝ) (z : State) : ℝ := defect (z.1 : Bloch) (z.2 : Bloch)/(3*kappa r)
def psi (r : ℝ) (z : State) : ℝ := fSEP r z - VInfinity r z

def SeparatelyConvex (u : State → ℝ) : Prop :=
  ∀ (actor : Bool) (z : State) (n : ℕ) (s : Split n (active actor z)),
    u z ≤ (∑ i, s.w i * u (place actor (s.x i) (passive actor z)))

set_option maxHeartbeats 2000000 in
-- Compact hypographs and finite grafting are proved in the same declaration.
/-- Exact finite-tree semantics of the source iteration, with attained five-point
operators at every finite stage and no regularity assumption at infinity. -/
theorem source_bellman_finite_tree_identity (r : ℝ) (hr : 0 < r)
    (hlo : 1 / 2 < r ^ 2) (hhi : r ^ 2 < 2) :
    (IsCompact (K_s r)) ∧
    (∀ n, Admissible r (V r n)) ∧
    (∀ n z, V r n z ≤ V r (n+1) z) ∧
    (∀ n actor z,
      (∃ s : Split 5 (active actor z),
        fiveValue actor (V r n) z =
          ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ∧
      (∀ m (s : Split m (active actor z)),
        (∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor (V r n) z)) ∧
    (∀ n z,
      (∃ T : Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z)) ∧
    (∀ z, VInfinity r z = treeValue r z ∧
      0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ u : State → ℝ, SeparatelyConcave u →
      (∀ z, terminal r z ≤ u z) → ∀ z, VInfinity r z ≤ u z) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r) := by
  classical
  have hp : 0 < h r := by
    unfold h kappa
    positivity
  have continuous_response : ∀ i, Continuous (fun z : Bloch × Bloch =>
      matrixResponse r z.1 z.2 i) := by
    intro i
    unfold matrixResponse Q rho
    unfold D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix
    simp [dotProduct, Matrix.mulVec, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fun_prop
  have closedKs : IsClosed (K_s r) := by
    change IsClosed {z : Bloch × Bloch | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧
      ∀ i, matrixResponse r z.1 z.2 i = h r}
    have hc := (isClosed_eq (continuous_fst.norm) (continuous_const : Continuous
      (fun _ : Bloch × Bloch => (1 : ℝ)))).inter
      ((isClosed_eq (continuous_snd.norm) (continuous_const : Continuous
        (fun _ : Bloch × Bloch => (1 : ℝ)))).inter
        (isClosed_iInter fun i => isClosed_eq (continuous_response i)
          (continuous_const : Continuous (fun _ : Bloch × Bloch => h r))))
    convert hc using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
  have compactKs : IsCompact (K_s r) := by
    apply ((isCompact_closedBall (0 : Bloch) 1).prod
      (isCompact_closedBall (0 : Bloch) 1)).of_isClosed_subset closedKs
    intro z hz
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, hz.1,
      hz.2.1, le_refl, and_self] using (show ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 from ⟨hz.1,hz.2.1⟩)
  have init : Admissible r (terminal r) := by
    refine ⟨?_, ?_⟩
    · exact (closedKs.upperSemicontinuous_indicator hp.le).comp (by fun_prop)
    · intro z
      by_cases hz : ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r
      · simp [terminal, Set.indicator_of_mem hz, hp.le]
      · simp [terminal, Set.indicator_of_notMem hz, hp.le]
  have identity (actor : Bool) (z : State) : ∃ s : Split 5 (active actor z),
      (∀ u : State → ℝ, (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) = u z) := by
    let s : Split 5 (active actor z) :=
      ⟨fun i => if i = 0 then 1 else 0, fun _ => active actor z,
        by intro i; split <;> norm_num, by simp, by simp⟩
    refine ⟨s, ?_⟩
    intro u
    cases actor <;> simp [s, place, active, passive]
  have compression (actor : Bool) (u : State → ℝ) (z : State)
      (m : ℕ) (s : Split m (active actor z)) :
      ∃ t : Split 5 (active actor z),
        (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) =
        ∑ i, t.w i * u (place actor (t.x i) (passive actor z)) := by
    let F : Ball → ℝ := fun x => u (place actor x (passive actor z))
    let graph : Set (Bloch × ℝ) := {p | ∃ x : Ball, p = ((x : Bloch),F x)}
    let value := ∑ i, s.w i * F (s.x i)
    have hull : ((active actor z : Bloch),value) ∈ convexHull ℝ graph := by
      apply mem_convexHull_of_exists_fintype s.w (fun i => ((s.x i : Bloch),F (s.x i)))
        s.nonneg s.total
      · intro i; exact ⟨s.x i,rfl⟩
      · apply Prod.ext
        · simpa only [Prod.fst_sum, Prod.smul_fst] using s.mean
        · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, value]
    rw [convexHull_eq_union] at hull
    simp only [Set.mem_iUnion] at hull
    obtain ⟨t, ht, hi, hc⟩ := hull
    have card : Fintype.card t ≤ 5 := by
      have hdim := hi.card_le_finrank_succ
      have hsub := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → Bloch × ℝ)))
      have hamb : Module.finrank ℝ (Bloch × ℝ) = 4 := by
        simp [Module.finrank_prod, finrank_euclideanSpace_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card t ≤ Fintype.card (Fin 5) by simpa using card)
    rw [Finset.convexHull_eq] at hc
    obtain ⟨w, hw, hw1, hmean⟩ := hc
    choose x hx using fun i : t => ht i.property
    let W : Fin 5 → ℝ := Function.extend e (fun i : t => w i) (fun _ => 0)
    let X : Fin 5 → Ball := Function.extend e x (fun _ => active actor z)
    have W_e (i : t) : W (e i) = w i := e.injective.extend_apply _ _ i
    have X_e (i : t) : X (e i) = x i := e.injective.extend_apply _ _ i
    have W_zero (j : Fin 5) (hj : j ∉ Set.range e) : W j = 0 :=
      Function.extend_apply' _ _ _ hj
    have sum_transfer {E : Type} [AddCommMonoid E] (f : Fin 5 → E)
        (hf : ∀ j, j ∉ Set.range e → f j = 0) :
        (∑ j, f j) = ∑ i : t, f (e i) := by
      rw [← Finset.sum_image (fun i _ j _ h => e.injective h)]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hf j (by simpa using hj)
    have W_nonneg : ∀ j, 0 ≤ W j := by
      intro j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hj; rw [W_e]; exact hw i i.property
      · rw [W_zero j hj]
    have W_total : ∑ j, W j = 1 := by
      rw [sum_transfer W W_zero]
      simp only [W_e]
      simpa only [Finset.sum_coe_sort] using hw1
    have graph_mean : ∑ i : t, w i • (((x i : Bloch),F (x i)) : Bloch × ℝ) =
        ((active actor z : Bloch),value) := by
      simp_rw [← hx]
      rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hmean
      simpa only [Finset.univ_eq_attach, id_eq] using
        (show (∑ i ∈ t.attach, w i.val • i.val) = _ by
          rw [Finset.sum_attach (f := fun q : Bloch × ℝ => w q • q)]; exact hmean)
    have X_mean : ∑ j, W j • (X j : Bloch) = (active actor z : Bloch) := by
      rw [sum_transfer _ (by intro j hj; rw [W_zero j hj, zero_smul])]
      simp_rw [W_e, X_e]
      simpa only [Prod.fst_sum, Prod.smul_fst] using congrArg Prod.fst graph_mean
    refine ⟨⟨W,X,W_nonneg,W_total,X_mean⟩, ?_⟩
    change value = ∑ j, W j * F (X j)
    rw [sum_transfer _ (by intro j hj; rw [W_zero j hj, zero_mul])]
    simp_rw [W_e, X_e]
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using
      (congrArg Prod.snd graph_mean).symm
  -- The compact hypograph supplies attained operators and joint USC.
  have step (actor : Bool) (u : State → ℝ) (hu : Admissible r u) :
      Admissible r (fiveValue actor u) ∧
      (∀ z, u z ≤ fiveValue actor u z) ∧
      (∀ z, ∃ s : Split 5 (active actor z), fiveValue actor u z =
        ∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ∧
      (∀ z m (s : Split m (active actor z)),
        (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor u z) := by
    let mean : (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) → Bloch := fun p => ∑ i, p.1.val i • (p.2.1 i : Bloch)
    let height : (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) → ℝ := fun p => ∑ i, p.1.val i * (p.2.2 i : ℝ)
    let feasible : State → Set (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) := fun z => {p | mean p = (active actor z : Bloch) ∧
      ∀ i, (p.2.2 i : ℝ) ≤ u (place actor (p.2.1 i) (passive actor z))}
    have cm : Continuous mean := by
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp ((continuous_apply i).comp
          (continuous_fst.comp continuous_snd)))
    have ch : Continuous height := by
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp ((continuous_apply i).comp
          (continuous_snd.comp continuous_snd)))
    have ca : Continuous (fun z : State => (active actor z : Bloch)) := by
      cases actor <;> simp only [active, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    have cp (i : Fin 5) : Continuous (fun q : State × (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) =>
        (place actor (q.2.2.1 i) (passive actor q.1), (q.2.2.2 i : ℝ))) := by
      cases actor <;> simp only [place, passive, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    have closedFamily : IsClosed {q : State × (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) | q.2 ∈ feasible q.1} := by
      have hc := (isClosed_eq (cm.comp continuous_snd) (ca.comp continuous_fst)).inter
        (isClosed_iInter fun i => hu.1.IsClosed_hypograph.preimage (cp i))
      convert hc using 1
      ext q
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        feasible, Function.comp_apply]
    have closedFeasible (z : State) : IsClosed (feasible z) := by
      exact closedFamily.preimage (continuous_const.prodMk continuous_id)
    have compactFeasible (z : State) : IsCompact (feasible z) :=
      (closedFeasible z).isCompact
    have rewardBounds (z : State) (m : ℕ) (s : Split m (active actor z)) :
        0 ≤ (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ∧
        (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ≤ h r := by
      refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (s.nonneg i) (hu.2 _).1), ?_⟩
      calc
        _ ≤ ∑ i, s.w i * h r := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hu.2 _).2 (s.nonneg i)
        _ = h r := by rw [← Finset.sum_mul, s.total, one_mul]
    have bounded (z : State) : BddAbove {t | ∃ s : Split 5 (active actor z),
        t = ∑ i, s.w i * u (place actor (s.x i) (passive actor z))} := by
      refine ⟨h r, ?_⟩
      rintro t ⟨s,rfl⟩; exact (rewardBounds z 5 s).2
    have le_value (z : State) (s : Split 5 (active actor z)) :
        (∑ i, s.w i * u (place actor (s.x i) (passive actor z))) ≤ fiveValue actor u z :=
      le_csSup (bounded z) ⟨s,rfl⟩
    have graphParam (z : State) (s : Split 5 (active actor z)) :
        ∃ p ∈ feasible z, height p =
          ∑ i, s.w i * u (place actor (s.x i) (passive actor z)) := by
      refine ⟨(⟨s.w,s.nonneg,s.total⟩,s.x,
        fun i => ⟨u (place actor (s.x i) (passive actor z)),hu.2 _⟩), ?_, rfl⟩
      exact ⟨s.mean,fun _ => le_rfl⟩
    have nonempty (z : State) : (feasible z).Nonempty := by
      obtain ⟨s,_⟩ := identity actor z
      obtain ⟨p,hp,_⟩ := graphParam z s
      exact ⟨p,hp⟩
    have attainment (z : State) : ∃ s : Split 5 (active actor z),
        fiveValue actor u z = ∑ i, s.w i * u (place actor (s.x i) (passive actor z)) := by
      obtain ⟨p,hp,hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
        (nonempty z) (compactFeasible z) (ch.upperSemicontinuous.upperSemicontinuousOn _)
      let s : Split 5 (active actor z) := ⟨p.1.val,p.2.1,p.1.property.1,p.1.property.2,hp.1⟩
      have raise : height p ≤ ∑ i, s.w i * u (place actor (s.x i) (passive actor z)) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hp.2 i) (s.nonneg i)
      obtain ⟨q,hq,hqv⟩ := graphParam z s
      have eqh : height p = ∑ i, s.w i * u (place actor (s.x i) (passive actor z)) :=
        le_antisymm raise (hqv ▸ hmax hq)
      refine ⟨s, le_antisymm ?_ (le_value z s)⟩
      apply csSup_le
      · obtain ⟨s',_⟩ := identity actor z
        exact ⟨_,s',rfl⟩
      · rintro t ⟨s',rfl⟩
        obtain ⟨q,hq,hqv⟩ := graphParam z s'
        rw [← eqh, ← hqv]
        exact hmax hq
    have usc : UpperSemicontinuous (fiveValue actor u) := by
      apply upperSemicontinuous_iff_IsClosed_hypograph.mpr
      let closedSet : Set ((State × ℝ) × (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r)))) :=
        {q | q.2 ∈ feasible q.1.1 ∧ q.1.2 ≤ height q.2}
      have hc : IsClosed closedSet := by
        exact (closedFamily.preimage (by fun_prop : Continuous
          (fun q : (State × ℝ) × (stdSimplex ℝ (Fin 5) × (Fin 5 → Ball) × (Fin 5 → Set.Icc (0 : ℝ) (h r))) => (q.1.1,q.2)))).inter
          (isClosed_le (by fun_prop) (ch.comp continuous_snd))
      have heq : {q : State × ℝ | q.2 ≤ fiveValue actor u q.1} = Prod.fst '' closedSet := by
        ext q
        constructor
        · intro hq
          obtain ⟨s,hs⟩ := attainment q.1
          obtain ⟨p,hp,hpv⟩ := graphParam q.1 s
          exact ⟨(q,p),⟨hp,by rwa [hpv, ← hs]⟩,rfl⟩
        · rintro ⟨⟨z,p⟩,⟨hp,hv⟩,he⟩
          cases he
          let s : Split 5 (active actor z.1) :=
            ⟨p.1.val,p.2.1,p.1.property.1,p.1.property.2,hp.1⟩
          exact hv.trans ((Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hp.2 i) (s.nonneg i)).trans (le_value z.1 s))
      rw [heq]
      exact isClosedMap_fst_of_compactSpace _ hc
    refine ⟨⟨usc,?_⟩,?_,attainment,?_⟩
    · intro z
      obtain ⟨s,hs⟩ := attainment z
      rw [hs]; exact rewardBounds z 5 s
    · intro z
      obtain ⟨s,hs⟩ := identity actor z
      rw [← hs u]; exact le_value z s
    · intro z m s
      obtain ⟨t,ht⟩ := compression actor u z m s
      rw [ht]; exact le_value z t
  have admissible : ∀ n, Admissible r (V r n) := by
    intro n
    induction n with
    | zero => exact init
    | succ n ih =>
      have ha := (step false (V r n) ih).1
      have hb := (step true (V r n) ih).1
      refine ⟨ha.1.sup hb.1,?_⟩
      intro z
      exact ⟨(ha.2 z).1.trans (le_max_left _ _), max_le (ha.2 z).2 (hb.2 z).2⟩
  have increasing (n : ℕ) (z : State) : V r n z ≤ V r (n+1) z :=
    ((step false (V r n) (admissible n)).2.1 z).trans (le_max_left _ _)
  have monotone (z : State) : Monotone (fun n => V r n z) :=
    monotone_nat_of_le_succ (fun n => increasing n z)
  have operators (n : ℕ) (actor : Bool) (z : State) :=
    (step actor (V r n) (admissible n)).2.2
  have optimal : ∀ n z,
      (∃ T : Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z) := by
    intro n
    induction n with
    | zero =>
      intro z
      refine ⟨⟨Tree.stop z,le_rfl,rfl⟩,?_⟩
      intro T hd
      cases T with
      | stop z => exact le_rfl
      | node actor z m s next => simp only [Tree.depth] at hd; omega
    | succ n ih =>
      intro z
      have graft (actor : Bool) : ∃ T : Tree z, T.depth ≤ n+1 ∧
          T.reward (terminal r) = fiveValue actor (V r n) z := by
        obtain ⟨s,hs⟩ := (operators n actor z).1 z
        choose T hd hv using fun i => (ih (place actor (s.x i) (passive actor z))).1
        refine ⟨Tree.node actor z 5 s T, ?_, ?_⟩
        · have hsup : Finset.univ.sup (fun i => (T i).depth) ≤ n :=
            Finset.sup_le fun i _ => hd i
          change 1 + Finset.univ.sup (fun i => (T i).depth) ≤ n+1
          omega
        · change (∑ i, s.w i * (T i).reward (terminal r)) = fiveValue actor (V r n) z
          simp_rw [hv]
          exact hs.symm
      refine ⟨?_,?_⟩
      · by_cases hmax : fiveValue true (V r n) z ≤ fiveValue false (V r n) z
        · obtain ⟨T,hd,hv⟩ := graft false
          exact ⟨T,hd,by simpa only [V,max_eq_left hmax] using hv⟩
        · obtain ⟨T,hd,hv⟩ := graft true
          exact ⟨T,hd,by simpa only [V,max_eq_right (le_of_not_ge hmax)] using hv⟩
      · intro T hd
        cases T with
        | stop z => exact monotone z (Nat.zero_le (n+1))
        | node actor z m s next =>
          have hchild (i : Fin m) : (next i).depth ≤ n := by
            have hl := Finset.le_sup (f := fun i => (next i).depth) (Finset.mem_univ i)
            change 1 + Finset.univ.sup (fun i => (next i).depth) ≤ n+1 at hd
            omega
          change (∑ i, s.w i * (next i).reward (terminal r)) ≤ V r (n+1) z
          calc
            _ ≤ ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z)) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
                ((ih _).2 (next i) (hchild i)) (s.nonneg i)
            _ ≤ fiveValue actor (V r n) z := (operators n actor z).2 z m s
            _ ≤ V r (n+1) z := by
              cases actor
              · exact le_max_left _ _
              · exact le_max_right _ _
  have stageBdd (z : State) : BddAbove (Set.range (fun n => V r n z)) :=
    ⟨h r,by rintro _ ⟨n,rfl⟩; exact ((admissible n).2 z).2⟩
  have stageLe (n : ℕ) (z : State) : V r n z ≤ VInfinity r z :=
    le_csSup (stageBdd z) (Set.mem_range_self n)
  have treeLe (z : State) (T : Tree z) : T.reward (terminal r) ≤ VInfinity r z :=
    ((optimal T.depth z).2 T le_rfl).trans (stageLe T.depth z)
  have treeBdd (z : State) : BddAbove {t | ∃ T : Tree z, t = T.reward (terminal r)} := by
    refine ⟨h r,?_⟩
    rintro _ ⟨T,rfl⟩
    exact ((optimal T.depth z).2 T le_rfl).trans (((admissible T.depth).2 z).2)
  have treeNe (z : State) : {t | ∃ T : Tree z, t = T.reward (terminal r)}.Nonempty :=
    ⟨terminal r z,Tree.stop z,rfl⟩
  have equalValue (z : State) : VInfinity r z = treeValue r z := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n,rfl⟩
      obtain ⟨T,_,hv⟩ := (optimal n z).1
      change V r n z ≤ treeValue r z
      rw [← hv]
      exact le_csSup (treeBdd z) ⟨T,rfl⟩
    · exact csSup_le (treeNe z) (by rintro _ ⟨T,rfl⟩; exact treeLe z T)
  have infinityBounds (z : State) : 0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r :=
    ⟨((admissible 0).2 z).1.trans (stageLe 0 z),
      csSup_le (Set.range_nonempty _) (by rintro _ ⟨n,rfl⟩; exact ((admissible n).2 z).2)⟩
  have approximation (z : State) (e : ℝ) (he : 0 < e) :
      ∃ T : Tree z, VInfinity r z - e < T.reward (terminal r) := by
    have hl : VInfinity r z - e < treeValue r z := by rw [← equalValue z]; linarith
    obtain ⟨t,⟨T,rfl⟩,ht⟩ := exists_lt_of_lt_csSup (treeNe z) hl
    exact ⟨T,ht⟩
  have concave : SeparatelyConcave (VInfinity r) := by
    intro actor z m s
    by_contra! bad
    let e := ((∑ i, s.w i * VInfinity r (place actor (s.x i) (passive actor z))) -
      VInfinity r z)/2
    have he : 0 < e := by dsimp [e]; linarith
    choose T hT using fun i => approximation (place actor (s.x i) (passive actor z)) e he
    let grafted := Tree.node actor z m s T
    have hg := treeLe z grafted
    have hh : (∑ i, s.w i * VInfinity r (place actor (s.x i) (passive actor z))) ≤
        grafted.reward (terminal r) + e := by
      calc
        _ ≤ ∑ i, s.w i * ((T i).reward (terminal r) + e) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (by linarith [hT i]) (s.nonneg i)
        _ = grafted.reward (terminal r) + e := by
          simp only [mul_add,Finset.sum_add_distrib, ← Finset.sum_mul,s.total,
            one_mul,grafted,Tree.reward]
    dsimp [e] at hh
    linarith
  have least (u : State → ℝ) (hu : SeparatelyConcave u)
      (hmajor : ∀ z, terminal r z ≤ u z) (z : State) : VInfinity r z ≤ u z := by
    have bound : ∀ (z : State) (T : Tree z), T.reward (terminal r) ≤ u z := by
      intro z T
      induction T with
      | stop z => exact hmajor z
      | node actor z m s next ih =>
        exact (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (ih i) (s.nonneg i)).trans (hu actor z m s)
    rw [equalValue z]
    exact csSup_le (treeNe z) (by rintro _ ⟨T,rfl⟩; exact bound z T)
  have kp : 0 < kappa r := by
    unfold kappa
    positivity
  have ballNorm (a : Ball) : ‖(a : Bloch)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using a.property
  have sep_nonneg (z : State) : 0 ≤ fSEP r z := by
    have hi := real_inner_le_norm (z.1 : Bloch) (z.2 : Bloch)
    have hm : ‖(z.1 : Bloch)‖ * ‖(z.2 : Bloch)‖ ≤ 1 :=
      (mul_le_mul (ballNorm z.1) (ballNorm z.2) (norm_nonneg _) (by norm_num)).trans (by norm_num)
    unfold fSEP defect
    apply div_nonneg
    · linarith
    · positivity
  have sep_affine (actor : Bool) (z : State) (m : ℕ) (s : Split m (active actor z)) :
      (∑ i, s.w i * fSEP r (place actor (s.x i) (passive actor z))) = fSEP r z := by
    have hi : (∑ i, s.w i * inner ℝ (s.x i : Bloch) (passive actor z : Bloch)) =
        inner ℝ (active actor z : Bloch) (passive actor z : Bloch) := by
      rw [← s.mean, sum_inner]
      simp_rw [real_inner_smul_left]
    cases actor
    · change Split m z.1 at s
      simp only [place,passive,active,Bool.false_eq_true,↓reduceIte] at hi ⊢
      unfold fSEP defect
      simp_rw [mul_div, mul_sub, mul_one, ← Finset.sum_div, Finset.sum_sub_distrib]
      rw [s.total,hi]
    · change Split m z.2 at s
      simp only [place,passive,active,↓reduceIte] at hi ⊢
      have hj : (∑ i, s.w i * inner ℝ (z.1 : Bloch) (s.x i : Bloch)) =
          inner ℝ (z.1 : Bloch) (z.2 : Bloch) := by
        rw [← s.mean,inner_sum]
        simp_rw [real_inner_smul_right]
      unfold fSEP defect
      simp_rw [mul_div,mul_sub,mul_one,← Finset.sum_div,Finset.sum_sub_distrib]
      rw [s.total,hj]
  have sep_flat (z : State) (hz : ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r) :
      fSEP r z = h r := by
    have hg := (all_r_flat_geometry r hr hlo hhi).2.2.2.2 (z.1 : Bloch) (z.2 : Bloch) hz
    unfold fSEP
    rw [hg.2.2]
    unfold g h
    field_simp [ne_of_gt kp,ne_of_gt (by positivity : 0 < 1+kappa r)]
  have sep_major (z : State) : terminal r z ≤ fSEP r z := by
    by_cases hz : ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r
    · simp only [terminal,Set.indicator_of_mem hz]
      exact (sep_flat z hz).ge
    · simp only [terminal,Set.indicator_of_notMem hz]
      exact sep_nonneg z
  have sep_bound (z : State) : VInfinity r z ≤ fSEP r z :=
    least (fSEP r) (fun actor z m s => (sep_affine actor z m s).le) sep_major z
  have flat_values (z : State) (hz : ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r) :
      VInfinity r z = h r ∧ psi r z = 0 := by
    have hl := stageLe 0 z
    simp only [V,terminal,Set.indicator_of_mem hz] at hl
    have hu := sep_bound z
    rw [sep_flat z hz] at hu
    have hv := le_antisymm hu hl
    exact ⟨hv,by simp only [psi,sep_flat z hz,hv,sub_self]⟩
  have diag_values (n : Ball) (hn : ‖(n : Bloch)‖ = 1) :
      VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0 := by
    have hsep : fSEP r (n,n) = 0 := by
      simp [fSEP,defect,real_inner_self_eq_norm_sq,hn]
    have hv := le_antisymm (hsep ▸ sep_bound (n,n)) (infinityBounds (n,n)).1
    exact ⟨hv,by simp [psi,hsep,hv]⟩
  have convex : SeparatelyConvex (psi r) := by
    intro actor z m s
    have hj := concave actor z m s
    have ha := sep_affine actor z m s
    have he : (∑ i, s.w i * psi r (place actor (s.x i) (passive actor z))) =
        fSEP r z - ∑ i, s.w i * VInfinity r (place actor (s.x i) (passive actor z)) := by
      simp only [psi,mul_sub,Finset.sum_sub_distrib,ha]
    rw [he]
    unfold psi
    linarith
  refine ⟨compactKs,admissible,increasing,?_,optimal,?_,concave,least,?_,flat_values,
    diag_values,convex⟩
  · intro n actor z
    exact ⟨(operators n actor z).1 z,(operators n actor z).2 z⟩
  · intro z
    exact ⟨equalValue z,infinityBounds z⟩
  · intro z
    exact ⟨(infinityBounds z).1,sep_bound z,sub_nonneg.mpr (sep_bound z),
      sub_le_self _ (infinityBounds z).1⟩

end D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
