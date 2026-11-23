/- GID: D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/TwoTreeFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Oriented edges and exact circulation coordinates of recursive two-trees. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Circulations of recursive two-trees -/

open scoped BigOperators ENNReal

namespace SimpleGraph

/-- Indices of the oriented edges created in generation `d`. -/
abbrev TwoTreeFrontier : ℕ → Type
  | 0 => Fin 3
  | d + 1 => TwoTreeFrontier d × Bool

/-- Vertices after `d` rounds, with a different vertex for each insertion. -/
abbrev TwoTreeV : ℕ → Type
  | 0 => Fin 3
  | d + 1 => TwoTreeV d ⊕ TwoTreeFrontier d

instance (d : ℕ) : Fintype (TwoTreeFrontier d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ d ih => exact @instFintypeProd _ _ ih inferInstance

instance (d : ℕ) : Fintype (TwoTreeV d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ d ih => exact @instFintypeSum _ _ ih inferInstance

instance (d : ℕ) : Nonempty (TwoTreeV d) := by
  induction d with
  | zero => exact ⟨(0 : Fin 3)⟩
  | succ d ih => exact ih.map Sum.inl

/-- Source of a directed frontier edge. -/
def twoTreeSource : (d : ℕ) → TwoTreeFrontier d → TwoTreeV d
  | 0, e => e
  | d + 1, (e, false) => .inl (twoTreeSource d e)
  | _ + 1, (e, true) => .inr e

/-- Target of a directed frontier edge. -/
def twoTreeTarget : (d : ℕ) → TwoTreeFrontier d → TwoTreeV d
  | 0, e => (e : Fin 3) + 1
  | _ + 1, (e, false) => .inr e
  | d + 1, (e, true) => .inl (twoTreeTarget d e)
/-- Join each new vertex to its two specified old endpoints. -/
def twoTreeAttach {V I : Type*} (G : SimpleGraph V) (s t : I → V) : SimpleGraph (V ⊕ I) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr e => u = s e ∨ u = t e
    | .inr e, .inl u => u = s e ∨ u = t e
    | .inr _, .inr _ => False
  symm.symm a b := by
    intro h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := ⟨by rintro (a | e); exacts [G.loopless.irrefl a, id]⟩

/-- The graph obtained by attaching a vertex to each previous frontier edge at every round. -/
def twoTree : (d : ℕ) → SimpleGraph (TwoTreeV d)
  | 0 => ⊤
  | d + 1 => twoTreeAttach (twoTree d) (twoTreeSource d) (twoTreeTarget d)
/-- The core triangle and the triangles made at successive insertions. -/
abbrev TwoTreeTriangles : ℕ → Type
  | 0 => Unit
  | d + 1 => TwoTreeTriangles d ⊕ TwoTreeFrontier d

instance (d : ℕ) : Fintype (TwoTreeTriangles d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ d ih => exact @instFintypeSum _ _ ih inferInstance

instance (d : ℕ) : DecidableEq (TwoTreeTriangles d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ d ih =>
    letI := ih
    have ht : DecidableEq (TwoTreeFrontier d) := by
      induction d with
      | zero => exact inferInstanceAs (DecidableEq (Fin 3))
      | succ d ih =>
        letI := ih
        exact inferInstanceAs (DecidableEq (TwoTreeFrontier d × Bool))
    letI := ht
    exact inferInstanceAs (DecidableEq (TwoTreeTriangles d ⊕ TwoTreeFrontier d))

/-- Indices of all edges, retaining the orientation in which each edge was created. -/
abbrev TwoTreeEdges : ℕ → Type
  | 0 => Fin 3
  | d + 1 => TwoTreeEdges d ⊕ (TwoTreeFrontier d × Bool)

instance (d : ℕ) : Fintype (TwoTreeEdges d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ d ih => exact @instFintypeSum _ _ ih inferInstance

/-- Source of an oriented edge, including edges from earlier rounds. -/
def twoTreeEdgeSource : (d : ℕ) → TwoTreeEdges d → TwoTreeV d
  | 0, e => e
  | d + 1, .inl e => .inl (twoTreeEdgeSource d e)
  | d + 1, .inr e => twoTreeSource (d + 1) e

/-- Target of an oriented edge, including edges from earlier rounds. -/
def twoTreeEdgeTarget : (d : ℕ) → TwoTreeEdges d → TwoTreeV d
  | 0, e => (e : Fin 3) + 1
  | d + 1, .inl e => .inl (twoTreeEdgeTarget d e)
  | d + 1, .inr e => twoTreeTarget (d + 1) e

private noncomputable def signedBoundary {R V E : Type*}
    [AddCommGroup R] [Fintype E] (s t : E → V) (x : E → R) (v : V) : R := by
  classical
  exact (∑ e, if t e = v then x e else 0) - ∑ e, if s e = v then x e else 0

/-- Signed net inflow of an edge chain at each vertex. -/
noncomputable def twoTreeBoundary {R : Type*} [CommRing R] (d : ℕ) :
    (TwoTreeEdges d → R) →ₗ[R] (TwoTreeV d → R) where
  toFun := signedBoundary (twoTreeEdgeSource d) (twoTreeEdgeTarget d)
  map_add' x y := by
    classical
    funext v
    simp only [signedBoundary, Pi.add_apply]
    simp_rw [ite_add, add_ite, add_zero, zero_add, Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    classical
    funext v
    simp only [signedBoundary, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sub, Finset.mul_sum]
    simp_rw [mul_ite, mul_zero]

/-- Integral or real circulations, as the kernel of signed incidence on oriented edges. -/
abbrev TwoTreeCirculation (R : Type*) [CommRing R] (d : ℕ) :=
  LinearMap.ker (twoTreeBoundary (R := R) d)

private def extendFrontier {R : Type*} [Zero R] :
    (d : ℕ) → (TwoTreeFrontier d → R) → TwoTreeEdges d → R
  | 0, x => x
  | _ + 1, x => Sum.elim (fun _ => 0) x

private theorem boundary_extendFrontier {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeFrontier d → R) (v : TwoTreeV d) :
    twoTreeBoundary d (extendFrontier d x) v =
      signedBoundary (twoTreeSource d) (twoTreeTarget d) x v := by
  classical
  cases d with
  | zero => rfl
  | succ d => simp [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget,
      extendFrontier, Fintype.sum_sum_type]

private theorem boundary_fresh {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeEdges (d + 1) → R) (e : TwoTreeFrontier d) :
    twoTreeBoundary (d + 1) x (.inr e) = x (.inr (e, false)) - x (.inr (e, true)) := by
  classical
  simp [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget, twoTreeSource,
    twoTreeTarget, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]

private theorem boundary_old {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeEdges (d + 1) → R) (v : TwoTreeV d) :
    twoTreeBoundary (d + 1) x (.inl v) = twoTreeBoundary d (x ∘ Sum.inl) v +
      (∑ e, if twoTreeTarget d e = v then x (.inr (e, true)) else 0) -
      ∑ e, if twoTreeSource d e = v then x (.inr (e, false)) else 0 := by
  classical
  simp [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget, twoTreeSource,
    twoTreeTarget, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  abel

private theorem equal_children {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeCirculation R (d + 1)) (e : TwoTreeFrontier d) :
    x.val (.inr (e, true)) = x.val (.inr (e, false)) := by
  have h : twoTreeBoundary (d + 1) x.val (Sum.inr e) = 0 := congrFun x.property _
  rw [boundary_fresh, sub_eq_zero] at h
  exact h.symm

private def reduceChain {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeEdges (d + 1) → R) : TwoTreeEdges d → R :=
  (x ∘ Sum.inl) + extendFrontier d (fun e => x (.inr (e, false)))

private theorem reduced_balance {R : Type*} [CommRing R] (d : ℕ)
    (x : TwoTreeEdges (d + 1) → R) (h : ∀ e, x (.inr (e, true)) = x (.inr (e, false)))
    (v : TwoTreeV d) :
    twoTreeBoundary d (reduceChain d x) v = twoTreeBoundary (d + 1) x (.inl v) := by
  classical
  rw [reduceChain, map_add]
  change twoTreeBoundary d (x ∘ Sum.inl) v + twoTreeBoundary d (extendFrontier d _) v = _
  rw [boundary_extendFrontier, boundary_old]
  simp only [h, signedBoundary]
  abel

private def joinedChain {R : Type*} [CommRing R] (d : ℕ)
    (old : TwoTreeEdges d → R) (c : TwoTreeFrontier d → R) : TwoTreeEdges (d + 1) → R :=
  Sum.elim (old - extendFrontier d c) fun e => c e.1

private theorem reduce_join {R : Type*} [CommRing R] (d : ℕ)
    (old : TwoTreeEdges d → R) (c : TwoTreeFrontier d → R) :
    reduceChain d (joinedChain d old c) = old := by
  change (old - extendFrontier d c) + extendFrontier d c = old
  exact sub_add_cancel _ _

private noncomputable def splitCirculation {R : Type*} [CommRing R] (d : ℕ) :
    TwoTreeCirculation R (d + 1) ≃ₗ[R] TwoTreeCirculation R d × (TwoTreeFrontier d → R) where
  toFun x := (⟨reduceChain d x.val, by
    funext v
    rw [reduced_balance d x.val (equal_children d x)]
    exact congrFun x.property (.inl v)⟩, fun e => x.val (.inr (e, false)))
  invFun p := ⟨joinedChain d p.1.val p.2, by
    funext v
    rcases v with v | e
    · have hr := reduced_balance d (joinedChain d p.1.val p.2) (fun _ => rfl) v
      rw [reduce_join] at hr
      exact hr.symm.trans (congrFun p.1.property v)
    · rw [boundary_fresh]
      exact sub_self _⟩
  left_inv x := by
    apply Subtype.ext
    funext e
    rcases e with e | ⟨e, side⟩
    · change (x.val (.inl e) + extendFrontier d (fun j => x.val (.inr (j, false))) e) -
        extendFrontier d (fun j => x.val (.inr (j, false))) e = x.val (.inl e)
      exact add_sub_cancel_right _ _
    · cases side
      · rfl
      · exact (equal_children d x e).symm
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (reduce_join d p.1.val p.2)
    · rfl
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      funext e
      change reduceChain d (x.val + y.val) e = (reduceChain d x.val + reduceChain d y.val) e
      cases d with
      | zero => simp [reduceChain, extendFrontier]; abel
      | succ d => cases e <;> simp [reduceChain, extendFrontier] <;> abel
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      funext e
      change reduceChain d (a • x.val) e = (a • reduceChain d x.val) e
      cases d with
      | zero => simp [reduceChain, extendFrontier, smul_add]
      | succ d => cases e <;> simp [reduceChain, extendFrontier, smul_add]
    · rfl

private theorem core_coefficients {R : Type*} [CommRing R] (x : TwoTreeCirculation R 0)
    (e : Fin 3) : x.val e = x.val 0 := by
  have h₁ : x.val 0 - x.val 1 = 0 := by
    simpa [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget,
      Fin.sum_univ_three, show (1 : Fin 3) + 1 = 2 by decide, show (2 : Fin 3) + 1 = 0 by decide]
      using congrFun x.property (1 : Fin 3)
  have h₂ : x.val 1 - x.val 2 = 0 := by
    simpa [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget,
      Fin.sum_univ_three, show (1 : Fin 3) + 1 = 2 by decide, show (2 : Fin 3) + 1 = 0 by decide]
      using congrFun x.property (2 : Fin 3)
  fin_cases e
  · rfl
  · exact (sub_eq_zero.mp h₁).symm
  · exact ((sub_eq_zero.mp h₁).trans (sub_eq_zero.mp h₂)).symm

private noncomputable def coreCirculation {R : Type*} [CommRing R] :
    TwoTreeCirculation R 0 ≃ₗ[R] (Unit → R) where
  toFun x _ := x.val 0
  invFun c := ⟨fun _ => c (), by
    funext v
    change twoTreeBoundary 0 (fun _ => c ()) v = 0
    fin_cases v <;> simp [twoTreeBoundary, signedBoundary, twoTreeEdgeSource, twoTreeEdgeTarget,
      Fin.sum_univ_three, show (1 : Fin 3) + 1 = 2 by decide, show (2 : Fin 3) + 1 = 0 by decide]⟩
  left_inv x := Subtype.ext (funext fun e => (core_coefficients x e).symm)
  right_inv _ := funext fun u => by cases u; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Remove the latest insertion triangles before reading the old coordinates. -/
noncomputable def twoTreeCirculationCoordinates (R : Type*) [CommRing R] :
    (d : ℕ) → TwoTreeCirculation R d ≃ₗ[R] (TwoTreeTriangles d → R)
  | 0 => coreCirculation
  | d + 1 => (splitCirculation d).trans <|
      ((twoTreeCirculationCoordinates R d).prodCongr (LinearEquiv.refl R _)).trans
        (LinearEquiv.sumArrowLequivProdArrow (TwoTreeTriangles d) (TwoTreeFrontier d) R R).symm

/-- An edge either belongs to the old graph or joins a new vertex to one of its parents. -/
noncomputable def twoTreeAttachEdges {V I : Type*} (G : SimpleGraph V) (s t : I → V) :
    (G.edgeSet ⊕ (Σ e : I, {u : V // u = s e ∨ u = t e})) ≃ (twoTreeAttach G s t).edgeSet := by
  let embed : V ↪ V ⊕ I := ⟨Sum.inl, Sum.inl_injective⟩
  let f : (G.edgeSet ⊕ (Σ e : I, {u : V // u = s e ∨ u = t e})) →
      (twoTreeAttach G s t).edgeSet :=
    Sum.elim (fun e => ⟨Sym2.map embed e.1, by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind
      exact he⟩) fun e => ⟨s(.inl e.2.1, .inr e.1), e.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro (⟨a, ha⟩ | ⟨e, u, hu⟩) (⟨b, hb⟩ | ⟨j, v, hv⟩) h
    · exact congrArg Sum.inl (Subtype.ext (Sym2.map.injective embed.injective
        (congrArg Subtype.val h)))
    · exfalso
      have heq := congrArg Subtype.val h
      induction a using Sym2.ind
      simpa [f, embed, Sym2.eq_iff] using heq
    · exfalso
      have heq := congrArg Subtype.val h.symm
      induction b using Sym2.ind
      simpa [f, embed, Sym2.eq_iff] using heq
    · have heq : s(Sum.inl u, Sum.inr e) = s(Sum.inl v, Sum.inr j) :=
        congrArg Subtype.val h
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, false_and, or_false] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rfl
  · rintro ⟨a, ha⟩
    induction a using Sym2.ind with
    | _ x y =>
      rcases x with x | e <;> rcases y with y | j
      · exact ⟨.inl ⟨s(x, y), ha⟩, rfl⟩
      · exact ⟨.inr ⟨j, x, ha⟩, rfl⟩
      · exact ⟨.inr ⟨e, y, ha⟩, Subtype.ext Sym2.eq_swap⟩
      · exact False.elim ha

/-- The two distinct parents of an insertion are indexed by its two child-edge directions. -/
noncomputable def twoTreeParents {V : Type*} {x y : V} (h : x ≠ y) :
    Bool ≃ {u : V // u = x ∨ u = y} :=
  Equiv.ofBijective (fun b => match b with
    | false => ⟨x, Or.inl rfl⟩
    | true => ⟨y, Or.inr rfl⟩)
    ⟨by rintro (_ | _) (_ | _) he <;> first | rfl | exact (h rfl).elim |
        exact (h (congrArg Subtype.val he)).elim |
        exact (h (congrArg Subtype.val he.symm)).elim,
      by rintro ⟨_, rfl | rfl⟩; exacts [⟨false, rfl⟩, ⟨true, rfl⟩]⟩

/-- The oriented dart corresponding to each frontier index. -/
def twoTreeFrontierDart (d : ℕ) (e : TwoTreeFrontier d) : (twoTree d).Dart where
  toProd := (twoTreeSource d e, twoTreeTarget d e)
  adj := by
    cases d with
    | zero =>
      change (e : Fin 3) ≠ e + 1
      exact (by decide : ∀ i : Fin 3, i ≠ i + 1) e
    | succ d =>
      obtain ⟨e, side⟩ := e
      cases side
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- The identification of the signed edge coordinates with the graph edges. -/
structure TwoTreeEdgeIdentification (d : ℕ) where
  equiv : TwoTreeEdges d ≃ (twoTree d).edgeSet
  endpoints (e : TwoTreeEdges d) :
    (equiv e).val = s(twoTreeEdgeSource d e, twoTreeEdgeTarget d e)

private noncomputable def coreEdges : TwoTreeEdgeIdentification 0 := by
  let f (e : Fin 3) : (twoTree 0).edgeSet :=
    ⟨s(e, e + 1), (twoTreeFrontierDart 0 e).adj⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro e j h
    have he : s(e, e + 1) = s(j, j + 1) := congrArg Subtype.val h
    have hinj : ∀ a b : Fin 3, s(a, a + 1) = s(b, b + 1) → a = b := by decide
    exact hinj e j he
  · intro z
    obtain ⟨z, hz⟩ := z
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := hz
      have hex : ∀ a b : Fin 3, a ≠ b →
          ∃ e : Fin 3, s(e, e + 1) = s(a, b) := by decide
      obtain ⟨e, he⟩ := hex a b hab
      exact ⟨e, Subtype.ext he⟩

/-- Orientation indices enumerate the actual graph edges bijectively. -/
noncomputable def twoTreeEdgeIdentification : (d : ℕ) → TwoTreeEdgeIdentification d
  | 0 => coreEdges
  | d + 1 => by
    let previous := twoTreeEdgeIdentification d
    let s := twoTreeSource d
    let t := twoTreeTarget d
    let parents : (TwoTreeFrontier d × Bool) ≃
        (Σ e : TwoTreeFrontier d, {u : TwoTreeV d // u = s e ∨ u = t e}) :=
      (Equiv.sigmaEquivProd (TwoTreeFrontier d) Bool).symm.trans
        (Equiv.sigmaCongrRight fun e => twoTreeParents (twoTreeFrontierDart d e).fst_ne_snd)
    refine ⟨(previous.equiv.sumCongr parents).trans (twoTreeAttachEdges (twoTree d) s t), ?_⟩
    rintro (e | ⟨e, side⟩)
    · change Sym2.map Sum.inl (previous.equiv e).val =
        s(Sum.inl (twoTreeEdgeSource d e), Sum.inl (twoTreeEdgeTarget d e))
      rw [previous.endpoints]
      rfl
    · cases side
      · rfl
      · exact Sym2.eq_swap

/-- The core triangle and each insertion triangle as oriented chains. At its birth,
an insertion has coefficient one on both children and minus one on its parent. -/
noncomputable def twoTreeTriangleChain (R : Type*) [CommRing R] :
    (d : ℕ) → TwoTreeTriangles d → TwoTreeCirculation R d
  | 0, _ => coreCirculation.symm (fun _ => 1)
  | d + 1, .inl i => (splitCirculation d).symm (twoTreeTriangleChain R d i, 0)
  | d + 1, .inr e => by
    classical
    exact (splitCirculation d).symm (0, Pi.single e 1)

/-- Every oriented triangle has its own unit coordinate in the integral or real circulation
space. This identifies the recursively computed basis with actual triangle chains. -/
theorem twoTree_triangle_chain_coordinate (R : Type*) [CommRing R] (d : ℕ)
    (i : TwoTreeTriangles d) :
    twoTreeCirculationCoordinates R d (twoTreeTriangleChain R d i) = Pi.single i 1 := by
  classical
  induction d with
  | zero =>
    cases i
    apply funext
    rintro ⟨⟩
    simp [twoTreeCirculationCoordinates, twoTreeTriangleChain]
  | succ d ih =>
    rcases i with i | e
    · funext j
      rcases j with j | k
      · simpa [twoTreeCirculationCoordinates, twoTreeTriangleChain, Pi.single_apply]
          using congrFun (ih i) j
      · simp [twoTreeCirculationCoordinates, twoTreeTriangleChain, Pi.single_apply]
    · funext j
      rcases j with i | k
      · simp [twoTreeCirculationCoordinates, twoTreeTriangleChain, Pi.single_apply]
      · simp [twoTreeCirculationCoordinates, twoTreeTriangleChain, Pi.single_apply]

/-- The triangle-filling norm is the least sum of absolute values of coefficients
among representations by the oriented triangle chains. -/
noncomputable def twoTreeFillingNorm (d : ℕ) (z : TwoTreeCirculation ℝ d) : ℝ :=
  sInf {r | ∃ c : TwoTreeTriangles d → ℝ,
    (∑ i, c i • twoTreeTriangleChain ℝ d i) = z ∧ r = ∑ i, |c i|}

private theorem read_filling (d : ℕ) (c : TwoTreeTriangles d → ℝ) :
    twoTreeCirculationCoordinates ℝ d (∑ i, c i • twoTreeTriangleChain ℝ d i) = c := by
  classical
  funext k
  simp only [map_sum, map_smul, twoTree_triangle_chain_coordinate, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/-- Filling lengths have a unique coefficient vector, so the filling norm is
the sum norm of the circulation's triangle coordinates. -/
theorem twoTree_filling_norm_eq (d : ℕ) (z : TwoTreeCirculation ℝ d) :
    twoTreeFillingNorm d z = ‖WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ d z)‖ := by
  classical
  let c := twoTreeCirculationCoordinates ℝ d z
  have hfill : (∑ i, c i • twoTreeTriangleChain ℝ d i) = z :=
    (twoTreeCirculationCoordinates ℝ d).injective (read_filling d c)
  have hset : {r | ∃ c : TwoTreeTriangles d → ℝ,
      (∑ i, c i • twoTreeTriangleChain ℝ d i) = z ∧ r = ∑ i, |c i|} = {∑ i, |c i|} := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hc : a = c := (read_filling d a).symm.trans (congrArg _ ha)
      simp [hc]
    · intro hr
      exact ⟨c, hfill, hr⟩
  rw [twoTreeFillingNorm, hset, csInf_singleton, PiLp.norm_eq_sum (by simp : 0 < (1 : ℝ≥0∞).toReal)]
  simp [c, Real.norm_eq_abs]

/-- The cyclic order on the core triangle and on each insertion triangle. -/
def twoTreeOrientedTriangle : (d : ℕ) → TwoTreeTriangles d → TwoTreeV d × TwoTreeV d × TwoTreeV d
  | 0, _ => (0, 1, 2)
  | d + 1, .inl i =>
    let (a, b, c) := twoTreeOrientedTriangle d i
    (.inl a, .inl b, .inl c)
  | d + 1, .inr e => (.inl (twoTreeSource d e), .inr e, .inl (twoTreeTarget d e))

/-- The vertices of the corresponding graph triangle. -/
def twoTreeTriangleVertices (d : ℕ) (i : TwoTreeTriangles d) : Set (TwoTreeV d) :=
  let (a, b, c) := twoTreeOrientedTriangle d i
  {a, b, c}

/-- The sum of a gain around a triangle in its chosen cyclic order. -/
def twoTreeTriangleSum {R : Type*} [Add R] (d : ℕ) (g : TwoTreeV d → TwoTreeV d → R)
    (i : TwoTreeTriangles d) : R :=
  let (a, b, c) := twoTreeOrientedTriangle d i
  g a b + g b c + g c a

private theorem triangle_edges (d : ℕ) (i : TwoTreeTriangles d) :
    let (a, b, c) := twoTreeOrientedTriangle d i
    (twoTree d).Adj a b ∧ (twoTree d).Adj b c ∧ (twoTree d).Adj c a := by
  induction d with
  | zero =>
    change (0 : Fin 3) ≠ 1 ∧ (1 : Fin 3) ≠ 2 ∧ (2 : Fin 3) ≠ 0
    decide
  | succ d ih =>
    rcases i with i | e
    · obtain ⟨a, b, c⟩ := twoTreeOrientedTriangle d i
      exact ih i
    · exact ⟨Or.inl rfl, Or.inr rfl, (twoTreeFrontierDart d e).adj.symm⟩

private theorem core_triangle_vertices (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : ({a, b, c} : Set (Fin 3)) = {0, 1, 2} := by
  ext x
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;>
    simp_all [Set.mem_insert_iff]

private theorem image_triangle (d : ℕ) (i : TwoTreeTriangles d) :
    twoTreeTriangleVertices (d + 1) (.inl i) =
      Sum.inl '' twoTreeTriangleVertices d i := by
  unfold twoTreeTriangleVertices
  cases twoTreeOrientedTriangle d i
  simp [twoTreeOrientedTriangle, Set.image_insert_eq]

/-- Every triangle in the graph is a core or insertion triangle. -/
private theorem triangles_classify (d : ℕ) (a b c : TwoTreeV d)
    (hab : (twoTree d).Adj a b) (hbc : (twoTree d).Adj b c) (hac : (twoTree d).Adj a c) :
    ∃ i : TwoTreeTriangles d, twoTreeTriangleVertices d i = {a, b, c} := by
  induction d with
  | zero =>
    exact ⟨(), (core_triangle_vertices a b c hab.ne hbc.ne hac.ne).symm⟩
  | succ d ih =>
    let G := twoTree d
    let s := twoTreeSource d
    let t := twoTreeTarget d
    have parents (e : TwoTreeFrontier d) {u v : TwoTreeV d}
        (hu : u = s e ∨ u = t e) (hv : v = s e ∨ v = t e) (hne : u ≠ v) :
        (u = s e ∧ v = t e) ∨ (u = t e ∧ v = s e) := by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hne rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hne rfl).elim
    rcases a with a | e <;> rcases b with b | j <;> rcases c with c | k
    · obtain ⟨i, hi⟩ := ih a b c hab hbc hac
      refine ⟨.inl i, ?_⟩
      rw [image_triangle, hi]
      simp
    · refine ⟨.inr k, ?_⟩
      rcases parents k hac hbc (show G.Adj a b from hab).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals ext x; simp [twoTreeTriangleVertices, twoTreeOrientedTriangle, s, t]; tauto
    · refine ⟨.inr j, ?_⟩
      rcases parents j hab hbc (show G.Adj a c from hac).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals ext x; simp [twoTreeTriangleVertices, twoTreeOrientedTriangle, s, t]; tauto
    · exact hbc.elim
    · refine ⟨.inr e, ?_⟩
      rcases parents e hab hac (show G.Adj b c from hbc).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals ext x; simp [twoTreeTriangleVertices, twoTreeOrientedTriangle, s, t]; tauto
    · exact hac.elim
    · exact hab.elim
    · exact hab.elim

/-- The indices give exactly the triangles in the graph, with an oriented traversal for each. -/
theorem twoTree_triangles_classify (d : ℕ) :
    (∀ a b c, (twoTree d).Adj a b → (twoTree d).Adj b c → (twoTree d).Adj a c →
      ∃ i : TwoTreeTriangles d, twoTreeTriangleVertices d i = {a, b, c}) ∧
    (∀ i : TwoTreeTriangles d, let (a, b, c) := twoTreeOrientedTriangle d i
      (twoTree d).Adj a b ∧ (twoTree d).Adj b c ∧ (twoTree d).Adj c a) :=
  ⟨triangles_classify d, triangle_edges d⟩

/-- Extend old gains by prescribing the oriented defect on each inserted triangle. -/
def twoTreeInsertionGain {V I E : Type*} [AddCommGroup E] [DecidableEq V]
    (s t : I → V) (old : V → V → E) (τ : I → E) : V ⊕ I → V ⊕ I → E
  | .inl u, .inl v => old u v
  | .inl u, .inr e => if u = s e then 0 else -(old (s e) (t e) + τ e)
  | .inr e, .inl u => if u = s e then 0 else old (s e) (t e) + τ e
  | .inr _, .inr _ => 0

/-- The gain with prescribed oriented triangle sums, in the gauge that uses zero
on the first child of each insertion and on the first two core edges. -/
noncomputable def twoTreeTriangleGain {E : Type*} [AddCommGroup E] :
    (d : ℕ) → (TwoTreeTriangles d → E) → TwoTreeV d → TwoTreeV d → E
  | 0, τ, u, v =>
    if (u : Fin 3) = 2 ∧ (v : Fin 3) = 0 then τ ()
    else if (u : Fin 3) = 0 ∧ (v : Fin 3) = 2 then -τ () else 0
  | d + 1, τ, u, v => by
    classical
    exact twoTreeInsertionGain (twoTreeSource d) (twoTreeTarget d)
      (twoTreeTriangleGain d (τ ∘ Sum.inl)) (τ ∘ Sum.inr) u v

private theorem frontier_pairing {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (d : ℕ) (x : TwoTreeFrontier d → R) (g : TwoTreeV d → TwoTreeV d → E) :
    (∑ e : TwoTreeEdges d, extendFrontier d x e • g (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) =
      ∑ e : TwoTreeFrontier d, x e • g (twoTreeSource d e) (twoTreeTarget d e) := by
  cases d with
  | zero => rfl
  | succ d =>
    simp [Fintype.sum_sum_type, extendFrontier, twoTreeEdgeSource, twoTreeEdgeTarget]

/-- Evaluating the normalized gain on an actual signed circulation gives exactly the
linear combination of the input triangle labels with the circulation's coefficients. -/
theorem twoTree_triangle_gain_pairing {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (d : ℕ) (τ : TwoTreeTriangles d → E) (z : TwoTreeCirculation R d) :
    (∑ e : TwoTreeEdges d, z.val e •
      twoTreeTriangleGain d τ (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) =
      ∑ i : TwoTreeTriangles d, twoTreeCirculationCoordinates R d z i • τ i := by
  classical
  induction d with
  | zero =>
    rw [Fin.sum_univ_three]
    simp [twoTreeEdgeSource, twoTreeEdgeTarget, twoTreeTriangleGain,
      show (1 : Fin 3) + 1 = 2 by decide, show (2 : Fin 3) + 1 = 0 by decide,
      core_coefficients z 2, twoTreeCirculationCoordinates, coreCirculation]
  | succ d ih =>
    let previous := (splitCirculation d z).1
    let c := (splitCirculation d z).2
    let g := twoTreeTriangleGain d (τ ∘ Sum.inl)
    have hz : (splitCirculation d).symm (previous, c) = z := (splitCirculation d).symm_apply_apply _
    have old (e : TwoTreeEdges d) : z.val (.inl e) = previous.val e - extendFrontier d c e := by
      rw [← hz]
      rfl
    have leftChild (e : TwoTreeFrontier d) : z.val (.inr (e, false)) = c e := rfl
    have rightChild (e : TwoTreeFrontier d) : z.val (.inr (e, true)) = c e := equal_children d z e
    have distinct (e : TwoTreeFrontier d) : twoTreeTarget d e ≠ twoTreeSource d e :=
      (twoTreeFrontierDart d e).snd_ne_fst
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [twoTreeEdgeSource, twoTreeEdgeTarget, twoTreeSource, twoTreeTarget,
      twoTreeTriangleGain, twoTreeInsertionGain, if_pos rfl, if_neg (distinct _), Fintype.sum_bool,
      old, leftChild, rightChild, smul_zero, add_zero, sub_smul, smul_add,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change ((∑ e, previous.val e • g (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) -
      ∑ e, extendFrontier d c e • g (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) +
      ((∑ e, c e • g (twoTreeSource d e) (twoTreeTarget d e)) + ∑ e, c e • τ (.inr e)) =
      (∑ i, twoTreeCirculationCoordinates R d previous i • τ (.inl i)) + ∑ e, c e • τ (.inr e)
    rw [frontier_pairing, ih (τ ∘ Sum.inl) previous]
    abel

end SimpleGraph
