/- GID: D5/S3/Quantum/Recovery/PurifiedLocalPath
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PurifiedLocalPath
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual observed paths with mixed product ancillas factor into accumulated local maps with inaccessible garbage. -/

import D5.S3.Quantum.Recovery.RetainedLocalProtocol
import D5.S3.Quantum.Recovery.ProductPrefixRigidity
import D5.S3.Quantum.Foundation.FiniteDensityPurification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]

/-- Each new inaccessible index belongs only to the actual actor. Other
holders acquire only a singleton coordinate, canonically equivalent to no change. -/
def LocalHidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) (a : A) : Type :=
  { u : Unit // a = J.actor } → Hidden J y

noncomputable instance localHiddenFintype {d : A → ℕ} (J : Instrument d)
    (y : Fin J.outcomes) (a : A) : Fintype (LocalHidden J y a) := by
  classical
  unfold LocalHidden
  infer_instance

def distributeHidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :
    Hidden J y ≃ ((a : A) → LocalHidden J y a) where
  toFun k _ _ := k
  invFun f := f J.actor ⟨(),rfl⟩
  left_inv _ := rfl
  right_inv f := by
    funext a h
    rcases h with ⟨u, h⟩
    subst a
    congr 1

/-- Holder-indexed accumulated matrices, together with the actual ordered
hidden stack and the explicit regrouping equivalence. No rigidity fields. -/
structure LocalFactors (H d : A → ℕ) where
  garbage : A → Type
  finiteGarbage : ∀ a, Fintype (garbage a)
  stack : Type
  finiteStack : Fintype stack
  regroup : stack ≃ ((a : A) → garbage a)
  matrix : (a : A) → Matrix (Fin (d a) × garbage a) (Fin (H a)) ℂ

attribute [instance] LocalFactors.finiteGarbage LocalFactors.finiteStack

variable {H d : A → ℕ}

def LocalFactors.advanceMatrix (F : LocalFactors H d) (J : Instrument d)
    (y : Fin J.outcomes) (a : A) :
    Matrix (Fin (J.output y a) × (LocalHidden J y a × F.garbage a)) (Fin (H a)) ℂ
  := by
    intro p x
    by_cases h : a = J.actor
    · subst a
      exact ∑ i, chosenKraus J y (p.2.1 ⟨(),rfl⟩) p.1 i *
        F.matrix J.actor (i,p.2.2) x
    · exact F.matrix a (Fin.cast (J.unchanged y a h) p.1, p.2.2) x

@[reducible] def LocalFactors.advance (F : LocalFactors H d) (J : Instrument d) (y : Fin J.outcomes) :
    LocalFactors H (J.output y) where
  garbage a := LocalHidden J y a × F.garbage a
  finiteGarbage a := inferInstance
  stack := Hidden J y × F.stack
  finiteStack := inferInstance
  regroup :=
    { toFun := fun k a => (distributeHidden J y k.1 a, F.regroup k.2 a)
      invFun := fun f => ((distributeHidden J y).symm (fun a => (f a).1),
        F.regroup.symm (fun a => (f a).2))
      left_inv := fun k => by simp
      right_inv := fun f => by simp }
  matrix := F.advanceMatrix J y

/-- Product amplitudes on the actual ordered hidden coordinates. -/
def LocalFactors.amplitude (F : LocalFactors H d) (q : Coordinates d × F.stack)
    (x : Coordinates H) : ℂ :=
  D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap (fun a => Fin (H a)) F.matrix
    (fun a => (q.1 a, F.regroup q.2 a)) x

/-- All-matrix linear extension, keeping the spectator row/column untouched. -/
def LocalFactors.lift {R : Type} (F : LocalFactors H d) (X : State R H) :
    RetainedState R F.stack d := fun p q =>
  ∑ x : Coordinates H, ∑ z : Coordinates H,
    F.amplitude (p.1.2,p.2) x * X (p.1.1,x) (q.1.1,z) *
      star (F.amplitude (q.1.2,q.2) z)

/-- A prefix is selected only through observed outcomes of the existing tree. -/
inductive ObservedPath {Feedback : Type} : {d : A → ℕ} → Tree Feedback d → Type
  | here {d : A → ℕ} {T : Tree Feedback d} : ObservedPath T
  | next {d : A → ℕ} {J : Instrument d} {child : ∀ y, Tree Feedback (J.output y)}
      (y : Fin J.outcomes) (tail : ObservedPath (child y)) :
        ObservedPath (.node J child)

variable {Feedback : Type}

def ObservedPath.endDimensions : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → A → ℕ
  | d, _, .here => d
  | _, _, .next _ tail => tail.endDimensions

def ObservedPath.factors : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → LocalFactors H d → LocalFactors H path.endDimensions
  | _, _, .here, F => F
  | _, _, .next y tail, F => tail.factors (F.advance _ y)

def ObservedPath.stack : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → Type → Type
  | _, _, .here, G => G
  | _, _, .next (J := J) y tail, G => tail.stack (Hidden J y × G)

def ObservedPath.execute {R : Type} : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → {G : Type} → RetainedState R G d →
    RetainedState R (path.stack G) path.endDimensions
  | _, _, .here, _, X => X
  | _, _, .next y tail, _, X => tail.execute (retainedStep _ y X)

def ObservedPath.stackEquiv : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → (F : LocalFactors H d) →
    (path.factors F).stack ≃ path.stack F.stack
  | _, _, .here, F => Equiv.refl F.stack
  | _, _, .next y tail, F => tail.stackEquiv (F.advance _ y)

end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
noncomputable section
open scoped BigOperators
variable {A : Type} [Fintype A] [DecidableEq A]
variable {H d : A → ℕ} {R Feedback : Type}

/-- Chosen from the existing canonical density purification theorem, internally. -/
def ProductAncillas.purification (η : ProductAncillas A) (a : A) :
    Ket (Fin (η.dimension a) × Fin (η.dimension a)) :=
  (D5.S3.Quantum.Foundation.FiniteDensityPurification.purification (η.density a)).val

def ProductAncillas.rootFactors (η : ProductAncillas A) (H : A → ℕ) :
    LocalFactors H (fun a => H a * η.dimension a) where
  garbage a := Fin (η.dimension a)
  finiteGarbage a := inferInstance
  stack := (a : A) → Fin (η.dimension a)
  finiteStack := inferInstance
  regroup := Equiv.refl _
  matrix a p x := if (finProdFinEquiv.symm p.1).1 = x then
    η.purification a ((finProdFinEquiv.symm p.1).2, p.2) else 0

/-- The literal rectangular local edge, tensored with identity on old local garbage. -/
def LocalFactors.edge (F : LocalFactors H d) (J : Instrument d)
    (y : Fin J.outcomes) (a : A) :
    Matrix (Fin (J.output y a) × (LocalHidden J y a × F.garbage a))
      (Fin (d a) × F.garbage a) ℂ := by
  classical
  intro p q
  by_cases h : a = J.actor
  · subst a
    exact if q.2 = p.2.2 then chosenKraus J y (p.2.1 ⟨(),rfl⟩) p.1 q.1 else 0
  · exact if q = (Fin.cast (J.unchanged y a h) p.1, p.2.2) then 1 else 0

@[reducible] def ObservedPath.frame {d : A → ℕ} {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) : ℕ → (Σ d, LocalFactors H d)
  | 0 => ⟨d,F⟩
  | t+1 => match path with
    | .here => ⟨d,F⟩
    | .next y tail => tail.frame (F.advance _ y) t
termination_by structural t => t

abbrev ObservedPath.localCoordinates {T : Tree Feedback d} (path : ObservedPath T)
    (F : LocalFactors H d) (t : ℕ) (a : A) : Type :=
  Fin ((path.frame F t).1 a) × (path.frame F t).2.garbage a

noncomputable instance pathCoordinateFintype {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) (t : ℕ) (a : A) :
    Fintype (path.localCoordinates F t a) := inferInstanceAs
      (Fintype (Fin ((path.frame F t).1 a) × (path.frame F t).2.garbage a))

noncomputable instance pathCoordinateDecidableEq {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) (t : ℕ) (a : A) :
    DecidableEq (path.localCoordinates F t a) := Classical.decEq _

def ObservedPath.edges : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → (F : LocalFactors H d) → (t : ℕ) → (a : A) →
      Matrix (path.localCoordinates F (t+1) a) (path.localCoordinates F t a) ℂ
  | d, _, .here, F, 0, a => by
      classical
      exact (1 : Matrix (Fin (d a) × F.garbage a) (Fin (d a) × F.garbage a) ℂ)
  | d, _, .here, F, _+1, a => by
      classical
      exact (1 : Matrix (Fin (d a) × F.garbage a) (Fin (d a) × F.garbage a) ℂ)
  | _, _, .next (J := J) y _, F, 0, a => F.edge J y a
  | _, _, .next y tail, F, t+1, a => tail.edges (F.advance _ y) t a

def ObservedPath.actorAt [Nonempty A] : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → ℕ → A
  | _, _, .here, _ => Classical.choice inferInstance
  | _, _, .next (J := J) _ _, 0 => J.actor
  | _, _, .next _ tail, t+1 => tail.actorAt t

def ObservedPath.length : {d : A → ℕ} → {T : Tree Feedback d} → ObservedPath T → ℕ
  | _, _, .here => 0
  | _, _, .next _ tail => tail.length + 1

def ObservedPath.history : {d : A → ℕ} → {T : Tree Feedback d} → ObservedPath T → List ℕ
  | _, _, .here => []
  | _, _, .next y tail => y.val :: tail.history

def ObservedPath.endFeedback : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → Option Feedback
  | _, .leaf f, .here => some f
  | _, .node _ _, .here => none
  | _, _, .next _ tail => tail.endFeedback

@[instance_reducible] noncomputable def ObservedPath.stackFintype : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → {G : Type} → [Fintype G] → Fintype (path.stack G)
  | _, _, .here, _, inst => inst
  | _, _, .next _ tail, _, _ => tail.stackFintype
attribute [instance] ObservedPath.stackFintype

def ObservedPath.report {T : Tree Feedback d} (path : ObservedPath T)
    {G : Type} [Fintype G] (X : RetainedState R G d) : Terminal (Option Feedback) R A :=
  ⟨path.history, path.endFeedback, path.endDimensions, traceGarbage (path.execute X)⟩

/-- Actual mixed-ancilla local protocol prefixes factor through accumulated
holder-local matrices. The hidden-stack regrouping is explicit, root purification
is selected internally, and the report belongs to the original coarse prefix list.
No scalarity, isometry or probability-independence is assumed. -/
theorem purified_local_path_bridge [Nonempty A] [Fintype R]
    (P : Protocol Feedback H) (X : State R H) :
    let F := P.ancillas.rootFactors H
    traceGarbage (F.lift X) = appendAncillas P.ancillas X ∧
    (∀ a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (F.matrix a) = 1) ∧
    ∀ path : ObservedPath P.tree,
      path.report (F.lift X) ∈ coarsePrefixes P.tree (appendAncillas P.ancillas X) ∧
      path.execute (F.lift X) =
        ((path.factors F).lift X).submatrix
          (fun p => (p.1, (path.stackEquiv F).symm p.2))
          (fun p => (p.1, (path.stackEquiv F).symm p.2)) ∧
      path.frame F path.length = ⟨path.endDimensions, path.factors F⟩ ∧
      (∀ t a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated (fun a => Fin (H a))
        (path.localCoordinates F) (path.frame F 0).2.matrix (path.edges F) t a =
          (path.frame F t).2.matrix a) ∧
      (∀ t a, a ≠ path.actorAt t → ∃ e : path.localCoordinates F (t+1) a ≃
        path.localCoordinates F t a,
        path.edges F t a = (1 : Matrix (path.localCoordinates F t a)
          (path.localCoordinates F t a) ℂ).submatrix e id) := by
  classical
  have path_factorization {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) (X : State R H) :
      path.execute (F.lift X) =
        ((path.factors F).lift X).submatrix
          (fun p => (p.1, (path.stackEquiv F).symm p.2))
          (fun p => (p.1, (path.stackEquiv F).symm p.2)) := by
    classical
    have edge_amp {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) (p : R × Coordinates (J.output y))
        (k : Hidden J y) (g : F.stack) (x : Coordinates H) :
        (F.advance J y).amplitude (p.2,(k,g)) x =
          ∑ i, chosenKraus J y k (outputSplit R J y p).1 i *
            F.amplitude (((inputSplit R d J.actor).symm
              (i,(outputSplit R J y p).2)).2,g) x := by
      change (∏ a, F.advanceMatrix J y a
        (p.2 a, (distributeHidden J y k a, F.regroup g a)) (x a)) = _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ J.actor)]
      simp only [LocalFactors.advanceMatrix, dif_pos rfl]
      dsimp only [distributeHidden, Equiv.coe_fn_mk]
      simp only [dite_true]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [LocalFactors.amplitude, D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ J.actor)]
      have act : ((inputSplit R d J.actor).symm
          (i,(outputSplit R J y p).2)).2 J.actor = i := by
        simp [inputSplit, Equiv.piSplitAt]
      simp only [act]
      change (_ * _) * _ = _ * (_ * _)
      rw [mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro a ha
      have h : a ≠ J.actor := (Finset.mem_erase.mp ha).1
      simp [LocalFactors.advanceMatrix, h, inputSplit, outputSplit, Equiv.piSplitAt,
        Equiv.piCongrRight]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      have cast_val {m n : ℕ} (e : m = n) (v : Fin m) :
          (cast (congrArg Fin e) v).val = v.val := by cases e; rfl
      exact (cast_val (J.unchanged y a h) (p.2 a)).symm
    have edge {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) :
        retainedStep J y (F.lift X) = (F.advance J y).lift X := by
      ext p q
      dsimp only [retainedStep, LocalFactors.lift]
      conv_rhs =>
        arg 2; ext x; arg 2; ext z
        rw [edge_amp, edge_amp]
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      conv_lhs =>
        arg 2; ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      conv_lhs =>
        arg 2; ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      have rp : ((inputSplit R d J.actor).symm
        (i,(outputSplit R J y p.1).2)).1 = p.1.1 := rfl
      have rq : ((inputSplit R d J.actor).symm
        (j,(outputSplit R J y q.1).2)).1 = q.1.1 := rfl
      rw [rp, rq]
      ring
    induction path with
    | here => rfl
    | next y tail ih =>
      simp only [ObservedPath.execute, ObservedPath.factors, ObservedPath.stackEquiv]
      rw [edge]
      exact ih (F.advance _ y)
  have root_trace_check (η : ProductAncillas A) (X : State R H) :
      traceGarbage ((η.rootFactors H).lift X) = appendAncillas η X := by
    classical
    have amp (p : Coordinates (fun a => H a * η.dimension a))
        (g : (a : A) → Fin (η.dimension a)) (x : Coordinates H) :
        (η.rootFactors H).amplitude (p,g) x =
          if (fun a => (finProdFinEquiv.symm (p a)).1) = x then
            ∏ a, η.purification a ((finProdFinEquiv.symm (p a)).2, g a) else 0 := by
      change (∏ a, if (finProdFinEquiv.symm (p a)).1 = x a then
        η.purification a ((finProdFinEquiv.symm (p a)).2, g a) else 0) = _
      rw [Fintype.prod_ite_zero]
      simp only [funext_iff]
    have collapse (p q : (R × Coordinates (fun a => H a * η.dimension a)) ×
        ((a : A) → Fin (η.dimension a))) :
        (η.rootFactors H).lift X p q =
          X (p.1.1, fun a => (finProdFinEquiv.symm (p.1.2 a)).1)
            (q.1.1, fun a => (finProdFinEquiv.symm (q.1.2 a)).1) *
          ∏ a, (η.purification a ((finProdFinEquiv.symm (p.1.2 a)).2,p.2 a) *
            star (η.purification a ((finProdFinEquiv.symm (q.1.2 a)).2,q.2 a))) := by
      dsimp only [LocalFactors.lift]
      simp_rw [amp]
      simp only [apply_ite, ite_mul, zero_mul, mul_ite, mul_zero, star_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [star_prod, Finset.prod_mul_distrib]
      ring
    have local_trace (a : A) (u v : Fin (η.dimension a)) :
        (∑ g, η.purification a (u,g) * star (η.purification a (v,g))) =
          (η.density a).1 u v := by
      have h := (D5.S3.Quantum.Foundation.FiniteDensityPurification.purification (η.density a)).property.1
      have hc := congrArg (fun ρ => ρ.1 u v) h
      exact hc
    ext p q
    change (∑ g, (η.rootFactors H).lift X (p,g) (q,g)) = _
    simp_rw [collapse]
    rw [← Finset.mul_sum]
    erw [← Fintype.prod_sum (fun a (g : Fin (η.dimension a)) =>
      η.purification a ((finProdFinEquiv.symm (p.2 a)).2,g) *
      star (η.purification a ((finProdFinEquiv.symm (q.2 a)).2,g)))]
    simp_rw [local_trace]
    rfl
  have path_accumulation_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) :
      ∀ t a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated (fun a => Fin (H a))
        (path.localCoordinates F) (path.frame F 0).2.matrix (path.edges F) t a =
          (path.frame F t).2.matrix a := by
    classical
    have edge {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) (a : A) :
        (F.advance J y).matrix a = F.edge J y a * F.matrix a := by
      ext p x
      by_cases h : a = J.actor
      · subst a
        simp [LocalFactors.advance, LocalFactors.advanceMatrix, LocalFactors.edge,
          Matrix.mul_apply, Fintype.sum_prod_type]
      · simp [LocalFactors.advance, LocalFactors.advanceMatrix, LocalFactors.edge,
          h, Matrix.mul_apply]
    have step : ∀ t a, (path.frame F (t+1)).2.matrix a =
        path.edges F t a * (path.frame F t).2.matrix a := by
      induction path with
      | here => intro t a; cases t <;> simp [ObservedPath.frame, ObservedPath.edges]
      | next y tail ih =>
        intro t a
        cases t with
        | zero => exact edge F _ y a
        | succ t => exact ih (F.advance _ y) t a
    intro t a
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated]
      rw [ih]
      exact (step t a).symm
  have root_isometry_check (η : ProductAncillas A) (a : A) :
      D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((η.rootFactors H).matrix a) = 1 := by
    classical
    have hn : (∑ u, star (η.purification a u) * η.purification a u) = (1 : ℂ) := by
      have h := congrArg (fun r : ℝ => (r : ℂ)) (η.purification a).normalized'
      simpa only [Complex.ofReal_sum, Complex.ofReal_one, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self, Ket.coe_fun_eq, starRingEnd_apply] using h
    ext x z
    change (∑ p : Fin (H a * η.dimension a) × Fin (η.dimension a),
      star ((η.rootFactors H).matrix a p x) * (η.rootFactors H).matrix a p z) = _
    rw [← (Equiv.prodCongr (finProdFinEquiv :
      Fin (H a) × Fin (η.dimension a) ≃ Fin (H a * η.dimension a))
        (Equiv.refl (Fin (η.dimension a)))).sum_comp]
    simp only [Fintype.sum_prod_type]
    simp only [ProductAncillas.rootFactors, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map_apply]
    by_cases h : x = z
    · subst z
      simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Matrix.one_apply_eq]
      simpa only [Fintype.sum_prod_type] using hn
    · simp [apply_ite, h, Matrix.one_apply, eq_comm]
  have path_inactive_check {d : A → ℕ} {T : Tree Feedback d}
      (path : ObservedPath T) (F : LocalFactors H d) :
      ∀ t a, a ≠ path.actorAt t → ∃ e : path.localCoordinates F (t+1) a ≃
        path.localCoordinates F t a,
        path.edges F t a = (1 : Matrix (path.localCoordinates F t a)
          (path.localCoordinates F t a) ℂ).submatrix e id := by
    classical
    induction path with
    | here =>
      intro t a _
      cases t <;> refine ⟨Equiv.refl _, ?_⟩ <;> ext p q <;>
        simp only [ObservedPath.edges, Matrix.submatrix_apply, Equiv.refl_apply,
          id_eq, Matrix.one_apply] <;> split_ifs <;> simp_all <;> aesop
    | @next d J child y tail ih =>
      intro t a h
      cases t with
      | succ t => exact ih (F.advance J y) t a h
      | zero =>
        change a ≠ J.actor at h
        let e : (Fin (J.output y a) × (LocalHidden J y a × F.garbage a)) ≃
            (Fin (d a) × F.garbage a) :=
          { toFun := fun p => (Fin.cast (J.unchanged y a h) p.1, p.2.2)
            invFun := fun p => (Fin.cast (J.unchanged y a h).symm p.1,
              (fun u => (h u.2).elim, p.2))
            left_inv := fun p => by
              ext
              · simp
              · funext u; exact (h u.2).elim
              · rfl
            right_inv := fun p => by ext <;> simp }
        refine ⟨e, ?_⟩
        ext p q
        simp only [ObservedPath.edges, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
        simp only [LocalFactors.edge, dif_neg h, e]
        split_ifs <;> simp_all only [Equiv.coe_fn_mk, eq_comm, not_true_eq_false, not_false_eq_true] <;> aesop
  have endpoint_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) :
      path.frame F path.length = ⟨path.endDimensions, path.factors F⟩ := by
    induction path with
    | here => rfl
    | next y tail ih => exact ih (F.advance _ y)
  have actual_prefix_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T) :
      ∀ {G : Type} [Fintype G] (X : RetainedState R G d),
        path.report X ∈ retainedPrefixes T X := by
    induction path with
    | @here d T =>
      intro G _ X
      cases T <;> simp [ObservedPath.report, ObservedPath.history,
        ObservedPath.endFeedback, ObservedPath.endDimensions, ObservedPath.execute,
        retainedPrefixes] <;> congr 1 <;> exact Subsingleton.elim _ _
    | @next d J child y tail ih =>
      intro G _ X
      apply List.mem_cons_of_mem
      apply List.mem_flatten.mpr
      refine ⟨_, List.mem_ofFn.mpr ⟨y,rfl⟩, ?_⟩
      apply List.mem_map.mpr
      refine ⟨tail.report (retainedStep J y X), ih _, ?_⟩
      rfl
  refine ⟨root_trace_check P.ancillas X, root_isometry_check P.ancillas, ?_⟩
  intro path
  let F := P.ancillas.rootFactors H
  refine ⟨?_, path_factorization path F X, endpoint_check path F,
    path_accumulation_check path F, path_inactive_check path F⟩
  have h := actual_prefix_check path (F.lift X)
  rw [(recursive_coarse_retained P.tree (F.lift X)).2] at h
  simpa only [F, root_trace_check] using h

end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol
