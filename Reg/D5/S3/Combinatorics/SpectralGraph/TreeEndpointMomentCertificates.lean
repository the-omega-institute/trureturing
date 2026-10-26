import D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Order.ULift
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Whole-telescope audits of the actual polynomial-state observations. -/

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates

open _root_.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Polynomial SimpleGraph

universe u v w

abbrev Parameters := Σ K : Type u, Σ _ : Field K, Σ V : Type v,
  Σ _ : Fintype V, Σ _ : DecidableEq V, Σ _ : Matrix V V K, Σ _ : V, K × K

namespace Parameters
abbrev K (p : Parameters.{u,v}) := p.1
abbrev field (p : Parameters.{u,v}) : Field p.K := p.2.1
abbrev V (p : Parameters.{u,v}) := p.2.2.1
abbrev finite (p : Parameters.{u,v}) : Fintype p.V := p.2.2.2.1
abbrev equality (p : Parameters.{u,v}) : DecidableEq p.V := p.2.2.2.2.1
abbrev M (p : Parameters.{u,v}) : Matrix p.V p.V p.K := p.2.2.2.2.2.1
abbrev o (p : Parameters.{u,v}) : p.V := p.2.2.2.2.2.2.1
abbrev a (p : Parameters.{u,v}) : p.K := p.2.2.2.2.2.2.2.1
abbrev c (p : Parameters.{u,v}) : p.K := p.2.2.2.2.2.2.2.2
end Parameters

attribute [instance] Parameters.field Parameters.finite Parameters.equality

private abbrev pack {K : Type u} [Field K] {V : Type v} [Fintype V] [DecidableEq V]
    (M : Matrix V V K) (o : V) (a c : K) : Parameters.{u,v} :=
  ⟨K, inferInstance, V, inferInstance, inferInstance, M, o, a, c⟩

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.V → p.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p j => chainVector p.M p.o p.a p.c j) (fun e => nomatch e)

def zero : Realization signature.{u,v} :=
  realize signature (fun _ p _ _ => (0 : p.K)) (fun e => nomatch e)

def initial : Realization signature.{u,v} :=
  realize signature (fun _ p _ => Pi.single p.o 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro _
  let p : Parameters.{u,v} := pack
    (0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) (ULift.{u} ℚ)) (ULift.up ()) 0 1
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (ULift.up ())
  change chainVector (0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) (ULift.{u} ℚ))
    (ULift.up ()) 0 1 0 (ULift.up ()) =
      chainVector 0 (ULift.up ()) 0 1 1 (ULift.up ()) at hh
  simpa [chainVector, polynomialVector, chainPolynomial,
    affinePolynomial] using hh

namespace Pairing
abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {K : Type u} [Field K] {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W] [DecidableEq W]
    (M : Matrix V V K) (J : Matrix W W K) (hs : M.IsSymm) (ht : J.IsSymm)
    (o : V) (z : W) (a c : K) (d i j : ℕ)
    (hm : ∀ k ≤ d, (M ^ k) o o = (J ^ k) z z) (hd : i + j ≤ d),
    O.readout () (pack M o a c) i ⬝ᵥ O.readout () (pack M o a c) j =
      chainVector J z a c i ⬝ᵥ chainVector J z a c j

private theorem rejected : ¬ arena.{u,v,w}.Law zero := by
  intro h
  let K := ULift.{u} ℚ
  let V := ULift.{v} Unit
  let W := ULift.{w} Unit
  have hh := h (0 : Matrix V V K) (0 : Matrix W W K) (by simp) (by simp)
    (ULift.up ()) (ULift.up ()) 0 1 0 0 0 (by
      intro k hk
      have he : k = 0 := by omega
      simp only [he, pow_zero, Matrix.one_apply, ite_true]) (by omega)
  have hw : (ULift.up () : W) = default := Subsingleton.elim _ _
  simpa [zero, realize, pack, chainVector, polynomialVector, chainPolynomial,
    dotProduct, Matrix.col_apply, Matrix.one_apply, hw] using hh

def family : Registration arena.{u,v,w} (type_of% (@prefix_chain_pairing.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefix_chain_pairing.{u,v,w}, zero, rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zero, ?_, rfl, rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@prefix_chain_pairing.{u,v,w}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.prefix_chain_pairing.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.Pairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pairing

namespace Diagonal
abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {K : Type u} [Field K] {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W] [DecidableEq W]
    (M : Matrix V V K) (J : Matrix W W K) (hs : M.IsSymm) (ht : J.IsSymm)
    (o : V) (z : W) (a c : K) (d j : ℕ)
    (hm : ∀ k ≤ d, (M ^ k) o o = (J ^ k) z z) (hd : 2 * j + 1 ≤ d),
    O.readout () (pack M o a c) j ⬝ᵥ (M *ᵥ O.readout () (pack M o a c) j) =
      chainVector J z a c j ⬝ᵥ (J *ᵥ chainVector J z a c j)

private theorem rejected : ¬ arena.{u,v,w}.Law zero := by
  intro h
  let K := ULift.{u} ℚ
  let V := ULift.{v} Unit
  let W := ULift.{w} Unit
  have hh := h (1 : Matrix V V K) (1 : Matrix W W K) (by simp) (by simp)
    (ULift.up ()) (ULift.up ()) 0 1 1 0 (by intros; simp) (by omega)
  have hw : (ULift.up () : W) = default := Subsingleton.elim _ _
  simpa [zero, realize, pack, chainVector, polynomialVector, chainPolynomial,
    dotProduct, Matrix.col_apply, Matrix.one_apply, hw] using hh

def family : Registration arena.{u,v,w} (type_of% (@prefix_chain_diagonal.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefix_chain_diagonal.{u,v,w}, zero, rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zero, ?_, rfl, rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@prefix_chain_diagonal.{u,v,w}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.prefix_chain_diagonal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.Diagonal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Diagonal

private instance liftedOrder : IsStrictOrderedRing (ULift.{u} ℚ) :=
  Function.Injective.isStrictOrderedRing ULift.down rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) Iff.rfl Iff.rfl

namespace Rigidity
abbrev arena : Arena where
  signature := signature.{u,0}
  Law O := ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (J : Matrix (Fin n) (Fin n) K) (hJ : PositiveJacobi J) (a c : K) (hc : 0 < c)
    (hunit : ∀ j < r, O.readout () (pack J ⟨0, hn⟩ a c) j ⬝ᵥ O.readout () (pack J ⟨0, hn⟩ a c) j = 1)
    (hdiag : ∀ j < r,
      O.readout () (pack J ⟨0, hn⟩ a c) j ⬝ᵥ (J *ᵥ O.readout () (pack J ⟨0, hn⟩ a c) j) = a),
    r ≤ n ∧
      (∀ j < r, diagonalAt J j = a) ∧
      (∀ j, j + 1 < r → nextLink J j = c) ∧
      O.readout () (pack J ⟨0, hn⟩ a c) r ⬝ᵥ O.readout () (pack J ⟨0, hn⟩ a c) r =
        (c⁻¹ * nextLink J (r - 1)) ^ 2 * (if r < n then 1 else 0)

private theorem rejected : ¬ arena.{u}.Law initial := by
  intro h
  let K := ULift.{u} ℚ
  let J : Matrix (Fin 1) (Fin 1) K := 0
  have hJ : PositiveJacobi J := by
    constructor
    · exact Matrix.isSymm_zero
    · intro i j _; rfl
    · intro j hj; omega
  have hh := h (n := 1) (r := 1) (by omega) (by omega) J hJ 0 1 (by simp)
    (by intro j hj; simp [initial, realize, pack])
    (by intro j hj; simp [initial, realize, pack, J])
  have hn := hh.2.2.2
  norm_num [initial, realize, pack, nextLink] at hn

def family : Registration arena.{u} (type_of% (@positive_jacobi_prefix_rigidity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_jacobi_prefix_rigidity.{u}, initial, rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨initial, ?_, rfl, rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@positive_jacobi_prefix_rigidity.{u}) (Realization signature.{u,0}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.positive_jacobi_prefix_rigidity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.Rigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,0} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Rigidity

namespace Tree
abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (hG : G.IsTree) (hd : ∀ x, G.degree x ≤ 3)
    (o : V) (a c : K) (hc : 0 < c),
    ∃ (z : V) (p : G.Walk o z), p.IsPath ∧ IsStem p ∧
      1 ≤ p.length + 1 ∧ p.length + 1 ≤ Fintype.card V ∧
      (∀ i < p.length + 1, ∀ j < p.length + 1,
        O.readout () (pack (uniformMatrix G a c) o a c) i ⬝ᵥ
          O.readout () (pack (uniformMatrix G a c) o a c) j = if i = j then 1 else 0) ∧
      (∀ j < p.length + 1, O.readout () (pack (uniformMatrix G a c) o a c) j ⬝ᵥ
        (uniformMatrix G a c *ᵥ O.readout () (pack (uniformMatrix G a c) o a c) j) = a) ∧
      chainNorm (uniformMatrix G a c) o a c (p.length + 1) = (forward p).card ∧
      ((forward p).card = 0 ∨ (forward p).card = 2 ∨ (forward p).card = 3) ∧
      (0 < p.length → (forward p).card ≠ 3) ∧
      ((forward p).card = 0 → ∃ e : G ≃g pathGraph (p.length + 1), e o = 0) ∧
      (∀ j < p.length + 1, O.readout () (pack (uniformMatrix G a c) o a c) j =
        Pi.single (p.getVert j) 1) ∧
      O.readout () (pack (uniformMatrix G a c) o a c) (p.length + 1) =
        indicatorVector (forward p)

private theorem rejected : ¬ arena.{u,v}.Law initial := by
  intro h
  let K := ULift.{u} ℚ
  let V := ULift.{v} Unit
  have ht : (⊥ : SimpleGraph V).IsTree :=
    ⟨connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩, isAcyclic_bot⟩
  obtain ⟨z, p, hp, hs, hr, hb, hg, hd, hn, rest⟩ :=
    h (K := K) ht (by intro x; simp) (ULift.up ()) 0 1 (by simp)
  have hf := rest.2.2.2.2
  have he := congrFun hf (ULift.up ())
  simpa [initial, realize, pack, indicatorVector, forward] using he

def family : Registration arena.{u,v} (type_of% (@tree_first_departure.{v,u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tree_first_departure.{v,u}, initial, rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨initial, ?_, rfl, rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{rawV, rawK} :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@tree_first_departure.{rawV,rawK}) (Realization signature.{rawK,rawV}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.tree_first_departure.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates.Tree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rawK,rawV}⟩
  objectArena := .source ⟨arena.{rawK,rawV}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rawK,rawV} ⟨family.{rawK,rawV}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{rawK,rawV} actual.{rawK,rawV}.readout
    actual.{rawK,rawV}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Tree

end Reg.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates
