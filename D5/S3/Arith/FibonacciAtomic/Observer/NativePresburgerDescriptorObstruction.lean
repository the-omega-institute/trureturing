/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction.claim; result=D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction.result; claim=D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction.claim
   digest: All finite native trees admit no finite uniform native Presburger alpha descriptor interface. -/

import D5.S0.Computability.PresburgerFormulaGrowth
import D5.S0.Computability.PresburgerDecision
import D5.S0.Computability.NatPresburgerCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePresburgerDescriptorObstruction

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open FirstOrder Language
open PresburgerArithmetic PresburgerPatternGrowth PresburgerFormulaGrowth

universe u v

/-- The full epoch-zero interface: finite dependent tags, fixed numeric dimension
per tag, arbitrary admitted/valid tuples and maps, and every physical realization. -/
structure Interface (K : Type u) (T : Type v) (r : K → Nat) (q : T → Nat) where
  admitted : (k : K) → (Fin (r k) → Nat) → Prop
  valid : (t : T) → (Fin (q t) → Nat) → Prop
  Theta : (k : K) → {x // admitted k x} → Source
  Real : (t : T) → {y // valid t y} → Address → Prop
  reply : (k : K) → (t : T) → presburger.Formula (Fin (r k + (q t + 1)))
  source_cover : ∀ P : Source, ∃ k x, Theta k x = P
  address_cover : ∀ a : Address, ∃ t y, Real t y a
  exactness : ∀ k t x y a, Real t y a →
    ((reply k t).Realize (Fin.append x.val (Fin.cons 0 y.val)) ↔
      readout a (Theta k x) = .alpha)

/-- Existence of a uniform native Nat Presburger interface on all finite native
sources and all physical addresses. No numeric dimension must be positive. -/
def claim : Prop :=
  ∃ (K : Type) (T : Type), Finite K ∧ Finite T ∧
    ∃ (r : K → Nat) (q : T → Nat), Nonempty (Interface K T r q)

private theorem environment_free {m q : Nat} (x : Fin m → Nat) (y : Fin q → Nat) :
    NatPresburger.environment (Fin.append x (Fin.cons 0 y)) (default : Fin 0 → Nat) =
      List.ofFn (fun i => (x i : Int)) ++ (0 :: List.ofFn (fun i => (y i : Int))) := by
  simp only [NatPresburger.environment, List.ofFn_zero, List.reverse_nil, List.nil_append]
  rw [show (fun i => Int.ofNat (Fin.append x (Fin.cons 0 y) i)) =
    Fin.append (fun i => (x i : Int)) (Fin.cons 0 (fun i => (y i : Int))) by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp
      · intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp]
  rw [List.ofFn_fin_append, List.ofFn_cons]

/-- Refutation of the full interface, using the original Nat compiler, original
integer quantifier elimination, and the joint native-tree Growth obstruction. -/
private theorem interface_obstruction {K : Type u} {T : Type v} [Finite K] [Finite T]
    {r : K → Nat} {q : T → Nat} (I : Interface K T r q) : False := by
  classical
  let X (k : K) := {x // I.admitted k x}
  let Y (t : T) := {y // I.valid t y}
  let p (k : K) (t : T) := (NatPresburger.compile (I.reply k t)).quantifierEliminate
  let f (k : K) (t : T) (x : X k) (y : Y t) :=
    (p k t).eval (List.ofFn (fun i => (x.val i : Int)) ++
      (0 :: List.ofFn (fun i => (y.val i : Int))))
  apply NativePolynomialDescriptorObstruction.growth_obstruction
    (fun _ (_ : X _) => True) I.Theta I.Real f
    (fun k t => (budget (p k t)).1) (fun k t => (budget (p k t)).2)
  · intro k t
    exact qf_growth (p k t) (r k)
      (fun x : X k => List.ofFn (fun i => (x.val i : Int)))
      (fun y : Y t => 0 :: List.ofFn (fun i => (y.val i : Int))) (by intro x; simp)
  · intro P
    obtain ⟨k,x,hx⟩ := I.source_cover P
    exact ⟨k,x,trivial,hx⟩
  · exact I.address_cover
  · intro k t x y a _ ha
    have hc := NatPresburger.compile_correct (I.reply k t)
      (Fin.append x.val (Fin.cons 0 y.val)) (default : Fin 0 → Nat)
    have hqe := Formula.holds_iff_quantifierEliminate (NatPresburger.compile (I.reply k t))
      (NatPresburger.environment (Fin.append x.val (Fin.cons 0 y.val))
        (default : Fin 0 → Nat))
    rw [environment_free] at hc hqe
    apply hqe.symm.trans
    apply hc.trans
    have hex := I.exactness k t x y a ha
    unfold FirstOrder.Language.Formula.Realize at hex
    convert hex using 1
    apply Iff.of_eq
    congr 1
    exact Subsingleton.elim _ _

/-- The closed existential interface claim is refuted. Finite tag types in any
universe reindex to small finite types without restricting source or address maps. -/
theorem result : Not claim := by
  rintro ⟨K,T,hK,hT,r,q,⟨I⟩⟩
  letI := hK
  letI := hT
  exact interface_obstruction I

#print axioms environment_free
#print axioms interface_obstruction
#print axioms result

end D5.S3.Arith.FibonacciAtomic.Observer.NativePresburgerDescriptorObstruction
