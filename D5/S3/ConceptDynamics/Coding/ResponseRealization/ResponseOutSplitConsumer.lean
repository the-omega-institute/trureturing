/- SOURCE ONLY. Every new Lean declaration is UNCOMPILED.
Consumes the completed response P_B, without redoing table locality.
Imports OriginalResponse* from the authorized completed predecessor directory;
those files are unchanged and are not copied into this target. -/
import D5.S3.ConceptDynamics.Coding.ResponseGraphs.OriginalResponseGraph
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.OutSplitNumberedRecoding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResponseOutSplitConsumer

open EssentialWordRealization FiniteWindowTableCriterion
open OriginalResponseGraph OriginalResponseNumbering

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E)
variable {a b c d : ℕ} (pair : TablePair G G a b c d)

/-- The predecessor's actual edge equivalence supplies finiteness; no new
independent enumerator or quotient of the response edges is introduced. -/
instance numberedEdgeFintype : Fintype (CountedMatrixOverlap.Edge (matrix G pair)) :=
  Fintype.ofEquiv (ResponseEdge G pair) (edgeEquiv G pair).symm

private theorem responseEndpoints (e : CountedMatrixOverlap.Edge (matrix G pair)) :
    (graph G pair).source (edgeEquiv G pair e) = (vertexNumber G).symm e.source ∧
    (graph G pair).target (edgeEquiv G pair e) = (vertexNumber G).symm e.target := by
  have he := ((Fintype.equivFin (Fibre G pair e.source e.target)).symm e.number).property
  have hs : vertexNumber G ((graph G pair).source (edgeEquiv G pair e)) = e.source :=
    congrArg Prod.fst he
  have ht : vertexNumber G ((graph G pair).target (edgeEquiv G pair e)) = e.target :=
    congrArg Prod.snd he
  exact ⟨(vertexNumber G).injective (hs.trans ((vertexNumber G).apply_symm_apply _).symm),
    (vertexNumber G).injective (ht.trans ((vertexNumber G).apply_symm_apply _).symm)⟩

/-- Endpoint-preserving one-block graph code of the ACTUAL response output.
The endpoint equations are proved from the completed edge construction. -/
def responseCode (hf : Seam G G pair.f) :
    OutSplitConjugacyDecrease.Code (countedGraph G pair) G where
  vertex i := outputVertex G pair ((vertexNumber G).symm i)
  edge e := edgeOutput G pair (edgeEquiv G pair e)
  source e := by
    change G.source (edgeOutput G pair (edgeEquiv G pair e)) =
      outputVertex G pair ((vertexNumber G).symm e.source)
    rw [← (responseEndpoints G pair e).1]
    change G.source (edgeEquiv G pair e).val.2 =
      G.source (pair.f ((graph G pair).source (edgeEquiv G pair e)))
    rw [(edgeEquiv G pair e).property]
    rfl
  target e := by
    change G.target (edgeOutput G pair (edgeEquiv G pair e)) =
      outputVertex G pair ((vertexNumber G).symm e.target)
    rw [← (responseEndpoints G pair e).2]
    change G.target (edgeEquiv G pair e).val.2 =
      G.source (pair.f ((graph G pair).target (edgeEquiv G pair e)))
    rw [(edgeEquiv G pair e).property]
    exact hf (edgeWord G pair (edgeEquiv G pair e))

variable (hG : Essential G) (S : SameTableConjugacy pair)

private theorem responseOneBlock : ∀ z t,
    (numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG z).val t =
    (responseCode G pair (local_of_conjugacy hG hG pair S).seamG).edge (z.val t) := by
  intro z t
  rfl

private theorem responseInverseTable : ∀ y t,
    numberedRecover G pair (local_of_conjugacy hG hG pair S).seamF
      (historyWindow G y (t-((a+c:ℕ):ℤ)) ((a+c)+((b+d)+1)+1)) =
      ((numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG).symm y).val t := by
  let C := local_of_conjugacy hG hG pair S
  obtain ⟨_,_,_,_,_,_,hr,_⟩ := numbered_response_reduction G pair hG S
  intro y t
  have h := hr ((numberedOutput G pair S C.seamG).symm y) t
  rw [(numberedOutput G pair S C.seamG).apply_symm_apply] at h
  exact h

/-- The new actual horizontal conjugacy, with the two split graph types
specified by the constructions; not a supplied presentation witness. -/
def splitOutput :=
  OutSplitConjugacyDecrease.changed
    (responseCode G pair (local_of_conjugacy hG hG pair S).seamG)
    (numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG)

/-- Its total finite inverse table has radii (a+c,b+d), rather than the old
(a+c,b+d+1). Construction consumes actual recovery of P_B on all histories. -/
def splitRecover :=
  OutSplitConjugacyDecrease.recover
    (responseCode G pair (local_of_conjugacy hG hG pair S).seamG)
    (numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG)
    (responseOneBlock G pair hG S) hG (a+c) (b+d)
    (numberedRecover G pair (local_of_conjugacy hG hG pair S).seamF)
    (responseInverseTable G pair hG S)

/-- The new step preserves the literal original-h diagram inherited from
P_B; this helper is consumed by the original-domain example below. -/
theorem response_square (x : History G) :
    splitOutput G pair hG S
      (ActualOutSplit.lift (countedGraph G pair)
        (responseCode G pair (local_of_conjugacy hG hG pair S).seamG).edge
        (numberedLift G pair x)) = ActualOutSplit.lift G id (S.forward x) := by
  let C := local_of_conjugacy hG hG pair S
  obtain ⟨_,_,hp,_,_,_,_,_⟩ := numbered_response_reduction G pair hG S
  change OutSplitConjugacyDecrease.changed (responseCode G pair C.seamG)
    (numberedOutput G pair S C.seamG) _ = _
  rw [OutSplitConjugacyDecrease.square]
  exact congrArg (ActualOutSplit.lift G id) (hp x)

theorem response_recovery (z : History (ActualOutSplit.graph G id)) (t : ℤ) :
    splitRecover G pair hG S
      (historyWindow (ActualOutSplit.graph G id) z (t-((a+c:ℕ):ℤ)) ((a+c)+(b+d)+1)) =
      ((splitOutput G pair hG S).symm z).val t :=
  OutSplitConjugacyDecrease.recover_window
    (responseCode G pair (local_of_conjugacy hG hG pair S).seamG)
    (numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG)
    (responseOneBlock G pair hG S) hG (a+c) (b+d)
    (numberedRecover G pair (local_of_conjugacy hG hG pair S).seamF)
    (responseInverseTable G pair hG S) z t

end D5.S3.ConceptDynamics.Coding.ResponseOutSplitConsumer
