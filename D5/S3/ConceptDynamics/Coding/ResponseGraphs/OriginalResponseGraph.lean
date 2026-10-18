/- GID: D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original two-table response histories and their complete counted numbering. -/

/-
An actual two-table conjugacy is reduced to two projections of one finite
essential response graph. This is a higher-block/response-graph reduction,
not an elementary decomposition theorem. The input and output are the
original History G, with its original unit left shift.
-/
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OriginalResponseGraph

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E)
variable {a b c d : ℕ} (pair : TablePair G G a b c d)

private def front {N : ℕ} (w : LegalWord G (N + 1)) : LegalWord G N :=
  sliceWord G w 0 N (by omega)

private def back {N : ℕ} (w : LegalWord G (N + 1)) : LegalWord G N :=
  sliceWord G w 1 N (by omega)

private theorem front_window (x : History G) (i : ℤ) (N : ℕ) :
    front G (historyWindow G x i (N + 1)) = historyWindow G x i N := by
  simpa [front] using slice_historyWindow G x i (N + 1) 0 N (by omega)

private theorem back_window (x : History G) (i : ℤ) (N : ℕ) :
    back G (historyWindow G x i (N + 1)) = historyWindow G x (i + 1) N := by
  simpa [back] using slice_historyWindow G x i (N + 1) 1 N (by omega)

/-- All legal positive input words; no nonempty fibre is postulated. -/
abbrev Vertex := LegalWord G (a + b + 1)

/-- An actual word and its actual table response. Parallel word edges remain
distinct, even when they have identical endpoints and output. -/
abbrev ResponseEdge :=
  {z : LegalWord G (a + b + 1 + 1) × E // z.2 = pair.f (front G z.1)}

instance responseEdgeFintype : Fintype (ResponseEdge G pair) := by
  classical
  infer_instance

instance responseEdgeTopology : TopologicalSpace (ResponseEdge G pair) := ⊥
instance responseEdgeDiscrete : DiscreteTopology (ResponseEdge G pair) := ⟨rfl⟩

def edgeWord (e : ResponseEdge G pair) : LegalWord G (a + b + 1 + 1) := e.val.1
def edgeOutput (e : ResponseEdge G pair) : E := e.val.2

def makeEdge (w : LegalWord G (a + b + 1 + 1)) : ResponseEdge G pair :=
  ⟨(w, pair.f (front G w)), rfl⟩

private theorem edge_ext {e f : ResponseEdge G pair}
    (hw : edgeWord G pair e = edgeWord G pair f) : e = f := by
  rcases e with ⟨⟨w,u⟩,hu⟩
  rcases f with ⟨⟨w',u'⟩,hu'⟩
  change w = w' at hw
  subst w'
  have he : u = u' := hu.trans hu'.symm
  subst u'
  rfl

private def responseEdgeWordEquiv : ResponseEdge G pair ≃
    LegalWord G (a + b + 1 + 1) where
  toFun := edgeWord G pair
  invFun := makeEdge G pair
  left_inv e := edge_ext G pair rfl
  right_inv _ := rfl

def graph : DirectedMultigraph (Vertex (G := G) (a := a) (b := b))
    (ResponseEdge G pair) :=
  ⟨fun e => front G (edgeWord G pair e), fun e => back G (edgeWord G pair e)⟩

def inputVertex (w : Vertex (G := G) (a := a) (b := b)) : V :=
  G.source (w.edge ⟨a, by omega⟩)

def outputVertex (w : Vertex (G := G) (a := a) (b := b)) : V :=
  G.source (pair.f w)

private theorem projection_endpoints (hf : Seam G G pair.f) (e : ResponseEdge G pair) :
    G.source ((edgeWord G pair e).edge ⟨a, by omega⟩) =
        inputVertex G ((graph G pair).source e) ∧
    G.target ((edgeWord G pair e).edge ⟨a, by omega⟩) =
        inputVertex G ((graph G pair).target e) ∧
    G.source (edgeOutput G pair e) = outputVertex G pair ((graph G pair).source e) ∧
    G.target (edgeOutput G pair e) = outputVertex G pair ((graph G pair).target e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [inputVertex, graph, front, sliceWord]
  · simpa [inputVertex, graph, back, sliceWord, Nat.add_comm] using
      (edgeWord G pair e).legal ⟨a, by omega⟩
        (by change a + 1 < a + b + 1 + 1; omega)
  · change G.source e.val.2 = G.source (pair.f (front G (edgeWord G pair e)))
    rw [e.property]
    rfl
  · change G.target e.val.2 = G.source (pair.f (back G (edgeWord G pair e)))
    rw [e.property]
    exact hf (edgeWord G pair e)

private theorem adjacent_coordinate (z : History (graph G pair)) (i : ℤ)
    (j : ℕ) (hj : j < a + b + 1) :
    (edgeWord G pair (z.val i)).edge ⟨j + 1, by omega⟩ =
      (edgeWord G pair (z.val (i + 1))).edge ⟨j, by omega⟩ := by
  have he := congrArg (fun w : Vertex (G := G) (a := a) (b := b) =>
    w.edge ⟨j,hj⟩) (z.property i)
  simpa [graph, front, back, sliceWord, Nat.add_comm] using he

/- This induction is the no-spurious-histories step: an arbitrary legal
response history, not just a history already in the image, is reconstructed. -/
private theorem coordinate_to_zero (z : History (graph G pair))
    (j : ℕ) (hj : j < a + b + 1 + 1) (i : ℤ) :
    (edgeWord G pair (z.val i)).edge ⟨j,hj⟩ =
      (edgeWord G pair (z.val (i + (j : ℤ)))).edge ⟨0, by omega⟩ := by
  have H : ∀ k : ℕ, ∀ hk : k < a + b + 1 + 1, ∀ t : ℤ,
      (edgeWord G pair (z.val t)).edge ⟨k,hk⟩ =
        (edgeWord G pair (z.val (t + (k : ℤ)))).edge ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk t; simp
    | succ k ih =>
        intro hk t
        have hstep := adjacent_coordinate G pair z t k (by omega)
        have htail := ih (by omega) (t + 1)
        have ht : t + 1 + (k : ℤ) = t + ((k + 1 : ℕ) : ℤ) := by omega
        exact hstep.trans (by simpa only [ht] using htail)
  exact H j hj i

/-- Decode at the centre, so this projection has zero time correction. -/
def input (z : History (graph G pair)) : History G where
  val i := (edgeWord G pair (z.val i)).edge ⟨a, by omega⟩
  property i := by
    have hl := (edgeWord G pair (z.val i)).legal ⟨a, by omega⟩
      (by change a + 1 < a + b + 1 + 1; omega)
    exact hl.trans (congrArg G.source (adjacent_coordinate G pair z i a (by omega)))

private theorem coordinate_is_input (z : History (graph G pair)) (i : ℤ)
    (j : Fin (a + b + 1 + 1)) :
    (edgeWord G pair (z.val i)).edge j =
      (input G pair z).val (i - (a : ℤ) + (j.val : ℤ)) := by
  have h₀ := coordinate_to_zero G pair z j.val j.isLt i
  have h₁ := coordinate_to_zero G pair z a (by omega)
    (i - (a : ℤ) + (j.val : ℤ))
  have ht : i - (a : ℤ) + (j.val : ℤ) + (a : ℤ) = i + (j.val : ℤ) := by omega
  rw [ht] at h₁
  exact h₀.trans h₁.symm

def lift (x : History G) : History (graph G pair) where
  val i := makeEdge G pair (historyWindow G x (i - (a : ℤ)) (a + b + 1 + 1))
  property i := by
    change back G (historyWindow G x (i - (a : ℤ)) _) =
      front G (historyWindow G x (i + 1 - (a : ℤ)) _)
    rw [back_window, front_window]
    congr 1
    omega

private theorem input_lift (x : History G) : input G pair (lift G pair x) = x := by
  apply Subtype.ext
  funext i
  change x.val (i - (a : ℤ) + (a : ℤ)) = x.val i
  exact congrArg x.val (by omega)

private theorem lift_input (z : History (graph G pair)) :
    lift G pair (input G pair z) = z := by
  apply Subtype.ext
  funext i
  apply edge_ext G pair
  apply legalWord_ext
  funext j
  exact (coordinate_is_input G pair z i j).symm

private theorem lift_continuous : Continuous (lift G pair) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous (makeEdge G pair)).comp
    (historyWindow_continuous G (i - (a : ℤ)) _)

private theorem input_continuous : Continuous (input G pair) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous
    (fun e : ResponseEdge G pair => (edgeWord G pair e).edge ⟨a, by omega⟩)).comp
      ((continuous_apply i).comp continuous_subtype_val)

def inputHomeomorph : History G ≃ₜ History (graph G pair) where
  toFun := lift G pair
  invFun := input G pair
  left_inv := input_lift G pair
  right_inv := lift_input G pair
  continuous_toFun := lift_continuous G pair
  continuous_invFun := input_continuous G pair

def output (hf : Seam G G pair.f) (z : History (graph G pair)) : History G where
  val i := edgeOutput G pair (z.val i)
  property i := by
    have hs := hf (edgeWord G pair (z.val i))
    have hover : back G (edgeWord G pair (z.val i)) =
        front G (edgeWord G pair (z.val (i + 1))) := z.property i
    change G.target (z.val i).val.2 = G.source (z.val (i + 1)).val.2
    rw [(z.val i).property, (z.val (i + 1)).property]
    change G.target (pair.f (front G (edgeWord G pair (z.val i)))) =
      G.source (pair.f (front G (edgeWord G pair (z.val (i + 1)))))
    rw [← hover]
    exact hs

private theorem output_lift (S : SameTableConjugacy pair) (hf : Seam G G pair.f)
    (x : History G) : output G pair hf (lift G pair x) = S.forward x := by
  apply Subtype.ext
  funext i
  change pair.f (front G (historyWindow G x (i - (a : ℤ)) _)) = (S.forward x).val i
  rw [front_window]
  exact (S.forward_table x i).symm

private theorem output_all_histories (S : SameTableConjugacy pair)
    (hf : Seam G G pair.f) (z : History (graph G pair)) :
    output G pair hf z = S.forward (input G pair z) := by
  calc
    output G pair hf z = output G pair hf (lift G pair (input G pair z)) := by
      rw [lift_input]
    _ = S.forward (input G pair z) := output_lift G pair S hf _

private theorem output_continuous (hf : Seam G G pair.f) :
    Continuous (output G pair hf) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous (edgeOutput G pair)).comp
    ((continuous_apply i).comp continuous_subtype_val)

def outputHomeomorph (S : SameTableConjugacy pair) (hf : Seam G G pair.f) :
    History (graph G pair) ≃ₜ History G where
  toFun := output G pair hf
  invFun y := lift G pair (S.backward y)
  left_inv z := by
    change lift G pair (S.backward (output G pair hf z)) = z
    rw [output_all_histories G pair S hf, S.left_inverse, lift_input]
  right_inv y := by
    rw [output_lift G pair S hf, S.right_inverse]
  continuous_toFun := output_continuous G pair hf
  continuous_invFun := (lift_continuous G pair).comp S.continuous_backward

/-- A finite table of output words, not an existential recovery assertion.
Its domain is precisely [t-a-c,t+b+d+1], including both endpoints. -/
def inverseBlock (hg : Seam G G pair.g)
    (w : LegalWord G ((a + c) + (b + d + 1) + 1)) :
    LegalWord G (a + b + 1 + 1) :=
  mapBlock G G pair.g hg w (by omega) (by omega)

def recoverEdge (hg : Seam G G pair.g)
    (w : LegalWord G ((a + c) + (b + d + 1) + 1)) : ResponseEdge G pair :=
  makeEdge G pair (inverseBlock G pair hg w)

private theorem inverseBlock_window (S : SameTableConjugacy pair)
    (hg : Seam G G pair.g) (y : History G) (i : ℤ) :
    inverseBlock G pair hg
      (historyWindow G y (i - ((a + c : ℕ) : ℤ)) ((a + c) + (b + d + 1) + 1)) =
    historyWindow G (S.backward y) (i - (a : ℤ)) (a + b + 1 + 1) := by
  apply legalWord_ext
  funext j
  change pair.g (sliceWord G
    (historyWindow G y (i - ((a + c : ℕ) : ℤ)) _) j.val (c + d + 1) _) =
      (S.backward y).val (i - (a : ℤ) + (j.val : ℤ))
  rw [slice_historyWindow, S.backward_table]
  congr 1
  have ht : i - ((a + c : ℕ) : ℤ) + (j.val : ℤ) =
      i - (a : ℤ) + (j.val : ℤ) - (c : ℤ) := by omega
  rw [ht]

private theorem recovery (S : SameTableConjugacy pair)
    (hf : Seam G G pair.f) (hg : Seam G G pair.g)
    (z : History (graph G pair)) (i : ℤ) :
    recoverEdge G pair hg
      (historyWindow G (output G pair hf z) (i - ((a + c : ℕ) : ℤ))
        ((a + c) + (b + d + 1) + 1)) = z.val i := by
  apply edge_ext G pair
  change inverseBlock G pair hg _ = edgeWord G pair (z.val i)
  rw [inverseBlock_window G pair S hg, output_all_histories G pair S hf, S.left_inverse]
  apply legalWord_ext
  funext j
  exact (coordinate_is_input G pair z i j).symm

private theorem graph_essential (hG : Essential G) : Essential (graph G pair) := by
  constructor
  · intro w
    obtain ⟨x,hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    have hw : historyWindow G x 0 (a + b + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hx j
    refine ⟨(lift G pair x).val (a : ℤ), ?_⟩
    change front G (historyWindow G x ((a : ℤ) - (a : ℤ)) _) = w
    rw [front_window, sub_self, hw]
  · intro w
    obtain ⟨x,hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    have hw : historyWindow G x 0 (a + b + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hx j
    refine ⟨(lift G pair x).val ((a : ℤ) - 1), ?_⟩
    change back G (historyWindow G x ((a : ℤ) - 1 - (a : ℤ)) _) = w
    rw [back_window]
    have ht : (a : ℤ) - 1 - (a : ℤ) + 1 = 0 := by omega
    rw [ht, hw]

private theorem lift_shift (x : History G) :
    lift G pair (shift G x) = shift (graph G pair) (lift G pair x) := by
  apply Subtype.ext
  funext i
  apply edge_ext G pair
  apply legalWord_ext
  funext j
  change x.val (i - (a : ℤ) + (j.val : ℤ) + 1) =
    x.val (i + 1 - (a : ℤ) + (j.val : ℤ))
  exact congrArg x.val (by omega)

/-- Exact finite response-graph reduction. Both directions of the legal-history
identification and the actual finite inverse-table recovery are conclusions.
No elementary-factorization, resolvingness or desired diagram is a premise. -/
theorem response_reduction (hG : Essential G) (S : SameTableConjugacy pair) :
    let C := local_of_conjugacy hG hG pair S
    Essential (graph G pair) ∧
    Fintype.card (ResponseEdge G pair) = Fintype.card (LegalWord G (a + b + 1 + 1)) ∧
    (∀ x : History G, input G pair (lift G pair x) = x) ∧
    (∀ z : History (graph G pair), lift G pair (input G pair z) = z) ∧
    (∀ x : History G, outputHomeomorph G pair S C.seamG (inputHomeomorph G pair x) =
      S.forward x) ∧
    (∀ z : History (graph G pair),
      output G pair C.seamG z = S.forward (input G pair z)) ∧
    (∀ x : History G, lift G pair (shift G x) =
      shift (graph G pair) (lift G pair x)) ∧
    (∀ z : History (graph G pair),
      input G pair (shift (graph G pair) z) = shift G (input G pair z)) ∧
    (∀ z : History (graph G pair),
      output G pair C.seamG (shift (graph G pair) z) = shift G (output G pair C.seamG z)) ∧
    (∀ z : History (graph G pair), ∀ i : ℤ,
      recoverEdge G pair C.seamF
        (historyWindow G (output G pair C.seamG z) (i - ((a + c : ℕ) : ℤ))
          ((a + c) + (b + d + 1) + 1)) = z.val i) ∧
    (∀ e : ResponseEdge G pair,
      G.source ((edgeWord G pair e).edge ⟨a, by omega⟩) =
          inputVertex G ((graph G pair).source e) ∧
      G.target ((edgeWord G pair e).edge ⟨a, by omega⟩) =
          inputVertex G ((graph G pair).target e) ∧
      G.source (edgeOutput G pair e) = outputVertex G pair ((graph G pair).source e) ∧
      G.target (edgeOutput G pair e) = outputVertex G pair ((graph G pair).target e)) := by
  dsimp only
  refine ⟨graph_essential G pair hG, Fintype.card_congr (responseEdgeWordEquiv G pair),
    input_lift G pair, lift_input G pair, ?_, ?_, lift_shift G pair, ?_, ?_, ?_, ?_⟩
  · exact output_lift G pair S (local_of_conjugacy hG hG pair S).seamG
  · exact output_all_histories G pair S (local_of_conjugacy hG hG pair S).seamG
  · intro z; rfl
  · intro z; rfl
  · exact recovery G pair S (local_of_conjugacy hG hG pair S).seamG
      (local_of_conjugacy hG hG pair S).seamF
  · exact projection_endpoints G pair (local_of_conjugacy hG hG pair S).seamG

/-- Equality on the stated output interval synchronizes the entire actual
response edge, including its input word and response label. -/
theorem output_synchronizes (hG : Essential G) (S : SameTableConjugacy pair)
    (z z' : History (graph G pair)) (i : ℤ)
    (he : ∀ t : ℤ, i - ((a + c : ℕ) : ℤ) ≤ t →
      t ≤ i + ((b + d + 1 : ℕ) : ℤ) →
      (output G pair (local_of_conjugacy hG hG pair S).seamG z).val t =
      (output G pair (local_of_conjugacy hG hG pair S).seamG z').val t) :
    z.val i = z'.val i := by
  let C := local_of_conjugacy hG hG pair S
  have hw : historyWindow G (output G pair C.seamG z) (i - ((a + c : ℕ) : ℤ))
      ((a + c) + (b + d + 1) + 1) =
      historyWindow G (output G pair C.seamG z') (i - ((a + c : ℕ) : ℤ))
      ((a + c) + (b + d + 1) + 1) := by
    apply legalWord_ext
    funext j
    exact he _ (by omega) (by have := j.isLt; omega)
  rw [← recovery G pair S C.seamG C.seamF z i,
    ← recovery G pair S C.seamG C.seamF z' i, hw]

/-- Every legal finite output window, including one not supplied as an image
window, recovers a response edge with that window's literal central label. -/
theorem finite_recovery_label (hG : Essential G) (S : SameTableConjugacy pair)
    (w : LegalWord G ((a + c) + (b + d + 1) + 1)) :
    edgeOutput G pair (recoverEdge G pair (local_of_conjugacy hG hG pair S).seamF w) =
      w.edge ⟨a + c, by omega⟩ := by
  let C := local_of_conjugacy hG hG pair S
  obtain ⟨y,hy⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
  have hw : historyWindow G y 0 ((a + c) + (b + d + 1) + 1) = w := by
    apply legalWord_ext
    funext j
    simpa [historyWindow] using hy j
  let z := lift G pair (S.backward y)
  have ho : output G pair C.seamG z = y :=
    (output_lift G pair S C.seamG (S.backward y)).trans (S.right_inverse y)
  have hr := recovery G pair S C.seamG C.seamF z ((a + c : ℕ) : ℤ)
  rw [ho, sub_self, hw] at hr
  have hl := congrArg (edgeOutput G pair) hr
  have hc := congrArg (fun x : History G => x.val ((a + c : ℕ) : ℤ)) ho
  exact hl.trans (hc.trans (hy ⟨a + c, by omega⟩))

end D5.S3.ConceptDynamics.Coding.OriginalResponseGraph

namespace D5.S3.ConceptDynamics.Coding.OriginalResponseNumbering

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.OriginalResponseGraph
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap (CountMat Edge Path)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E)
variable {a b c d : ℕ} (pair : TablePair G G a b c d)

def vertexNumber : Vertex (G := G) (a := a) (b := b) ≃
    Fin (Fintype.card (Vertex (G := G) (a := a) (b := b))) :=
  Fintype.equivFin _

abbrev Size := Fintype.card (Vertex (G := G) (a := a) (b := b))

def endpoints (e : ResponseEdge G pair) :
    Fin (Size (G := G) (a := a) (b := b)) × Fin (Size (G := G) (a := a) (b := b)) :=
  (vertexNumber G ((graph G pair).source e), vertexNumber G ((graph G pair).target e))

/-- This subtype, rather than a positivity convention, is the actual edge
fibre. No vertices or zero matrix entries are discarded. -/
abbrev Fibre (i j : Fin (Size (G := G) (a := a) (b := b))) :=
  {e : ResponseEdge G pair // endpoints G pair e = (i,j)}

instance fibreFintype (i j : Fin (Size (G := G) (a := a) (b := b))) :
    Fintype (Fibre G pair i j) := by
  classical
  infer_instance

def matrix : CountMat (Size (G := G) (a := a) (b := b))
    (Size (G := G) (a := a) (b := b)) :=
  fun i j => Fintype.card (Fibre G pair i j)

private def countedEdgeSigma : Edge (matrix G pair) ≃
    (Σ p : Fin (Size (G := G) (a := a) (b := b)) ×
      Fin (Size (G := G) (a := a) (b := b)), Fin ((matrix G pair) p.1 p.2)) where
  toFun e := ⟨(e.source,e.target), e.number⟩
  invFun z := ⟨z.1.1,z.1.2,z.2⟩
  left_inv e := by cases e; rfl
  right_inv z := by rcases z with ⟨⟨i,j⟩,k⟩; rfl

/-- Decode a numbered edge to its original word/response edge. Every parallel
edge number is retained. `equivFin` is used in its actual α ≃ Fin(card α)
orientation, and inverted only on the decoding leg. -/
def edgeEquiv : Edge (matrix G pair) ≃ ResponseEdge G pair := by
  let fibres :
      (Σ p : Fin (Size (G := G) (a := a) (b := b)) ×
        Fin (Size (G := G) (a := a) (b := b)), Fin ((matrix G pair) p.1 p.2)) ≃
      (Σ p : Fin (Size (G := G) (a := a) (b := b)) ×
        Fin (Size (G := G) (a := a) (b := b)), Fibre G pair p.1 p.2) :=
    Equiv.sigmaCongrRight fun p => (Fintype.equivFin (Fibre G pair p.1 p.2)).symm
  exact (countedEdgeSigma G pair).trans
    (fibres.trans (Equiv.sigmaFiberEquiv (endpoints G pair)))

private theorem decode_endpoints (e : Edge (matrix G pair)) :
    endpoints G pair (edgeEquiv G pair e) = (e.source,e.target) := by
  exact ((Fintype.equivFin (Fibre G pair e.source e.target)).symm e.number).property

private theorem encode_endpoints (e : ResponseEdge G pair) :
    ((edgeEquiv G pair).symm e).source = (endpoints G pair e).1 ∧
    ((edgeEquiv G pair).symm e).target = (endpoints G pair e).2 := by
  have he := decode_endpoints G pair ((edgeEquiv G pair).symm e)
  rw [(edgeEquiv G pair).apply_symm_apply] at he
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

def countedGraph : DirectedMultigraph
    (Fin (Size (G := G) (a := a) (b := b))) (Edge (matrix G pair)) :=
  ⟨Edge.source,Edge.target⟩

/-- The ordinary finite graph and the literal existing counted Path subtype
are identified by edge numbers, with no quotient of parallel edges. -/
def numberHomeomorph : History (graph G pair) ≃ₜ Path (matrix G pair) where
  toFun z := ⟨fun t => (edgeEquiv G pair).symm (z.val t), by
    intro t
    rw [(encode_endpoints G pair (z.val t)).2,
      (encode_endpoints G pair (z.val (t + 1))).1]
    exact congrArg (vertexNumber G) (z.property t)⟩
  invFun z := ⟨fun t => edgeEquiv G pair (z.val t), by
    intro t
    apply (vertexNumber G).injective
    have h₀ := congrArg Prod.snd (decode_endpoints G pair (z.val t))
    have h₁ := congrArg Prod.fst (decode_endpoints G pair (z.val (t + 1)))
    exact h₀.trans ((z.property t).trans h₁.symm)⟩
  left_inv z := by
    apply Subtype.ext
    funext t
    exact (edgeEquiv G pair).apply_symm_apply _
  right_inv z := by
    apply Subtype.ext
    funext t
    exact (edgeEquiv G pair).symm_apply_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous (edgeEquiv G pair).symm).comp
      ((continuous_apply t).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous (edgeEquiv G pair)).comp
      ((continuous_apply t).comp continuous_subtype_val)

def numberedLift : History G ≃ₜ Path (matrix G pair) :=
  (inputHomeomorph G pair).trans (numberHomeomorph G pair)

def numberedOutput (S : SameTableConjugacy pair) (hf : Seam G G pair.f) :
    Path (matrix G pair) ≃ₜ History G :=
  (numberHomeomorph G pair).symm.trans (outputHomeomorph G pair S hf)

def numberedRecover (hg : Seam G G pair.g)
    (w : LegalWord G ((a + c) + (b + d + 1) + 1)) : Edge (matrix G pair) :=
  (edgeEquiv G pair).symm (recoverEdge G pair hg w)

private theorem zero_fibre (i j : Fin (Size (G := G) (a := a) (b := b))) :
    matrix G pair i j = 0 ↔ ¬ ∃ e : ResponseEdge G pair,
      endpoints G pair e = (i,j) := by
  change Fintype.card (Fibre G pair i j) = 0 ↔ _
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro hi ⟨e,he⟩
    exact hi.false ⟨e,he⟩
  · intro hi
    exact ⟨fun e => hi ⟨e.val,e.property⟩⟩

private theorem essential_numbering (h : Essential (graph G pair)) :
    Essential (countedGraph G pair) := by
  constructor
  · intro i
    obtain ⟨e,he⟩ := h.outgoing ((vertexNumber G).symm i)
    refine ⟨(edgeEquiv G pair).symm e, ?_⟩
    change ((edgeEquiv G pair).symm e).source = i
    rw [(encode_endpoints G pair e).1]
    change vertexNumber G ((graph G pair).source e) = i
    rw [he, (vertexNumber G).apply_symm_apply]
  · intro i
    obtain ⟨e,he⟩ := h.incoming ((vertexNumber G).symm i)
    refine ⟨(edgeEquiv G pair).symm e, ?_⟩
    change ((edgeEquiv G pair).symm e).target = i
    rw [(encode_endpoints G pair e).2]
    change vertexNumber G ((graph G pair).target e) = i
    rw [he, (vertexNumber G).apply_symm_apply]

/-- A concrete numbered finite essential response presentation of the
two-table conjugacy, with literal all-history projection and inverse bound.
This theorem says nothing about a finite elementary recoding word. -/
theorem numbered_response_reduction (hG : Essential G) (S : SameTableConjugacy pair) :
    let C := local_of_conjugacy hG hG pair S
    Essential (countedGraph G pair) ∧
    (∀ i j, matrix G pair i j = 0 ↔ ¬ ∃ e : ResponseEdge G pair,
      endpoints G pair e = (i,j)) ∧
    (∀ x : History G, numberedOutput G pair S C.seamG (numberedLift G pair x) =
      S.forward x) ∧
    (∀ z : Path (matrix G pair), ∀ t : ℤ,
      (numberedOutput G pair S C.seamG z).val t =
        edgeOutput G pair (edgeEquiv G pair (z.val t))) ∧
    (∀ z : Path (matrix G pair), numberedOutput G pair S C.seamG
      (CountedMatrixOverlap.shift (matrix G pair) z) =
      shift G (numberedOutput G pair S C.seamG z)) ∧
    (∀ x : History G, numberedLift G pair (shift G x) =
      CountedMatrixOverlap.shift (matrix G pair) (numberedLift G pair x)) ∧
    (∀ z : Path (matrix G pair), ∀ t : ℤ,
      numberedRecover G pair C.seamF
        (historyWindow G (numberedOutput G pair S C.seamG z)
          (t - ((a + c : ℕ) : ℤ)) ((a + c) + (b + d + 1) + 1)) = z.val t) ∧
    (∀ w : LegalWord G ((a + c) + (b + d + 1) + 1),
      edgeOutput G pair (edgeEquiv G pair (numberedRecover G pair C.seamF w)) =
        w.edge ⟨a + c, by omega⟩) := by
  let C := local_of_conjugacy hG hG pair S
  obtain ⟨hess,_,_,_,hcomp,_,hlift,_,_,hrec,_⟩ := response_reduction G pair hG S
  refine ⟨essential_numbering G pair hess, zero_fibre G pair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change outputHomeomorph G pair S C.seamG
      ((numberHomeomorph G pair).symm (numberHomeomorph G pair (inputHomeomorph G pair x))) = _
    rw [(numberHomeomorph G pair).symm_apply_apply]
    exact hcomp x
  · intro z t; rfl
  · intro z
    apply Subtype.ext
    rfl
  · intro x
    change numberHomeomorph G pair (lift G pair (shift G x)) = _
    rw [hlift]
    apply Subtype.ext
    rfl
  · intro z t
    have he := hrec ((numberHomeomorph G pair).symm z) t
    have hn := congrArg (edgeEquiv G pair).symm he
    change (edgeEquiv G pair).symm
      (recoverEdge G pair C.seamF
        (historyWindow G (output G pair C.seamG ((numberHomeomorph G pair).symm z))
          (t - ((a + c : ℕ) : ℤ)) ((a + c) + (b + d + 1) + 1))) = z.val t
    exact hn.trans ((edgeEquiv G pair).symm_apply_apply (z.val t))
  · intro w
    change edgeOutput G pair (edgeEquiv G pair ((edgeEquiv G pair).symm _)) = _
    rw [(edgeEquiv G pair).apply_symm_apply]
    exact finite_recovery_label G pair hG S w

end D5.S3.ConceptDynamics.Coding.OriginalResponseNumbering
