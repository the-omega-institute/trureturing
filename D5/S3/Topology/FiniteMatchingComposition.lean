/- GID: D5/S3/Topology/FiniteMatchingComposition
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteMatchingComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: First-return matching composition agrees with the glued network and internal loops. -/
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

/-!
Actual finite matching composition uses the canonical first-return pairing.
Half-edge seam contraction identifies it with the three-level gluing graph.
The internal components are transported by that same explicit equivalence.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.FiniteMatchingComposition

open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open Equiv

theorem sameCycle_involution {X : Type*} [Finite X] (p : Perm X)
    (hp : Function.Involutive p) (x y : X) :
    p.SameCycle x y ↔ y = x ∨ y = p x := by
  constructor
  · intro h
    obtain ⟨n,_,hn⟩ := h.exists_pow_eq'
    have hall : ∀ k : ℕ, (p^k) x = x ∨ (p^k) x = p x := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Perm.mul_apply]
        rcases ih with ih | ih
        · exact Or.inr (congrArg p ih)
        · exact Or.inl ((congrArg p ih).trans (hp x))
    simpa only [hn] using hall n
  · rintro (rfl | rfl)
    · exact Perm.SameCycle.refl _ _
    · exact (Perm.SameCycle.refl p x).apply_right

theorem eqvGen_iff_connected {X : Type*} (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r) (x y : X) :
    Relation.EqvGen (twoStep s r) x y ↔ Connected s r x y := by
  let R := fun u v : X => s u = v ∨ r u = v
  haveI : Std.Symm R := ⟨by
    intro u v h
    rcases h with h | h
    · exact Or.inl (by rw [← h]; exact hs u)
    · exact Or.inr (by rw [← h]; exact hr u)⟩
  change Relation.EqvGen (twoStep s r) x y ↔ Relation.ReflTransGen R x y
  constructor
  · intro h
    induction h with
    | rel u v h => exact .single (h.elim (fun h => Or.inl h.symm)
        (fun h => Or.inr h.symm))
    | refl => exact .refl
    | symm _ _ _ ih => exact symm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact .refl _
    | tail h hbc ih => exact .trans _ _ _ ih (.rel _ _
        (hbc.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)))

/-- Completeness of the library's actual first-return pairing for finite
cut matching components. The second involution may fix exposed endpoints. -/
theorem endpoint_component_iff {X : Type*} [Finite X] (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (x y : {z // r z = z}) :
    component (twoStep s r) x = component (twoStep s r) y ↔
      y = x ∨ y = endpointPairing s r hs hr x := by
  classical
  have hid : (1 : Perm {z // r z = z}).ofSubtype = (1 : Perm X) :=
    map_one Perm.ofSubtype
  have hfirst : (s*r).SameCycle (x:X) (y:X) ↔
      (endpointPairing s r hs hr).SameCycle x y := by
    simpa only [hid, mul_one] using endpoint_pairing_reattach_same_cycle s r hs hr
      (1 : Perm {z // r z = z}) x y
  have hsx : (s*r) (x:X) = s x := by
    simp only [Perm.mul_apply, x.property]
  have hcycle : (s*r).SameCycle (x:X) (s x) := by
    rw [← hsx]
    exact (Perm.SameCycle.refl (s*r) (x:X)).apply_right
  simp only [component, Quotient.eq]
  change Relation.EqvGen (twoStep s r) (x : X) (y : X) ↔ _
  rw [eqvGen_iff_connected s r hs hr,
    connected_iff_rotation_orbits s r hs hr]
  have horbit : ((s*r).SameCycle (x:X) (y:X) ∨ (s*r).SameCycle (s x) (y:X)) ↔
      (s*r).SameCycle (x:X) (y:X) := by
    constructor
    · exact fun h => h.elim id (fun h => hcycle.trans h)
    · exact Or.inl
  rw [horbit, hfirst, sameCycle_involution _ (endpoint_pairing_involutive s r hs hr)]

/-- One disjoint copy of each input matching's boundary. -/
abbrev Piece (N : ℕ) := Bool × Boundary N

def piecesMate {N : ℕ} (d e : Matching (Boundary N)) : Piece N → Piece N
  | (false,b) => (false,d.mate b)
  | (true,b) => (true,e.mate b)

theorem piecesMate_involutive {N : ℕ} (d e : Matching (Boundary N)) :
    Function.Involutive (piecesMate d e) := by
  rintro ⟨l,b⟩
  cases l <;> simp only [piecesMate, d.involutive b, e.involutive b]

theorem piecesMate_free {N : ℕ} (d e : Matching (Boundary N)) (x : Piece N) :
    piecesMate d e x ≠ x := by
  rcases x with ⟨l,b⟩
  cases l
  · exact fun h => d.fixedPointFree b (congrArg Prod.snd h)
  · exact fun h => e.fixedPointFree b (congrArg Prod.snd h)

def piecesPerm {N : ℕ} (d e : Matching (Boundary N)) : Perm (Piece N) where
  toFun := piecesMate d e
  invFun := piecesMate d e
  left_inv := piecesMate_involutive d e
  right_inv := piecesMate_involutive d e

/-- Glue d's bottom to e's top; leave d's top and e's bottom exposed.
Fixed points of this cut-wire involution are exactly the outer endpoints. -/
def seamMate {N : ℕ} : Piece N → Piece N
  | (false,(false,i)) => (false,(false,i))
  | (false,(true,i)) => (true,(false,i))
  | (true,(false,i)) => (false,(true,i))
  | (true,(true,i)) => (true,(true,i))

theorem seamMate_involutive (N : ℕ) : Function.Involutive (@seamMate N) := by
  rintro ⟨l,b,i⟩
  cases l <;> cases b <;> rfl

def seamPerm (N : ℕ) : Perm (Piece N) where
  toFun := seamMate
  invFun := seamMate
  left_inv := seamMate_involutive N
  right_inv := seamMate_involutive N

def exposedEquiv (N : ℕ) : Boundary N ≃ {z : Piece N // seamPerm N z = z} where
  toFun a := ⟨(a.1,a),by rcases a with ⟨b,i⟩; cases b <;> rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨l,b,i⟩,h⟩
    change seamMate (l, (b, i)) = (l, (b, i)) at h
    cases l <;> cases b <;> simp [seamMate] at h ⊢

def compositeMate {N : ℕ} (d e : Matching (Boundary N)) (a : Boundary N) : Boundary N :=
  (exposedEquiv N).symm
    (endpointPairing (piecesPerm d e) (seamPerm N)
      (piecesMate_involutive d e) (seamMate_involutive N) (exposedEquiv N a))

theorem compositeMate_involutive {N : ℕ} (d e : Matching (Boundary N)) :
    Function.Involutive (compositeMate d e) := by
  intro a
  apply (exposedEquiv N).injective
  simpa only [compositeMate, Equiv.apply_symm_apply] using
    endpoint_pairing_involutive (piecesPerm d e) (seamPerm N)
      (piecesMate_involutive d e) (seamMate_involutive N) (exposedEquiv N a)

theorem compositeMate_free {N : ℕ} (d e : Matching (Boundary N)) (a : Boundary N) :
    compositeMate d e a ≠ a := by
  intro h
  have he := congrArg (exposedEquiv N) h
  simp only [compositeMate, Equiv.apply_symm_apply] at he
  exact endpoint_pairing_fixed_point_free (piecesPerm d e) (seamPerm N)
    (piecesMate_involutive d e) (seamMate_involutive N) (piecesMate_free d e)
    (exposedEquiv N a) he

def composite {N : ℕ} (d e : Matching (Boundary N)) : Matching (Boundary N) :=
  ⟨compositeMate d e, compositeMate_involutive d e, compositeMate_free d e⟩

def halfEdgeStep {N : ℕ} (d e : Matching (Boundary N)) :=
  twoStep (piecesPerm d e) (seamPerm N)

def outerPiece {N : ℕ} (a : Boundary N) : Piece N := (a.1,a)

/-- The composite matching just constructed is EXACTLY the partner relation
on the actual glued components, rather than merely an involution on a set
of the correct size. -/
theorem composite_component_iff {N : ℕ} (d e : Matching (Boundary N))
    (a b : Boundary N) :
    component (halfEdgeStep d e) (outerPiece a) =
        component (halfEdgeStep d e) (outerPiece b) ↔
      b = a ∨ b = (composite d e).mate a := by
  have h := endpoint_component_iff (piecesPerm d e) (seamPerm N)
    (piecesMate_involutive d e) (seamMate_involutive N)
    (exposedEquiv N a) (exposedEquiv N b)
  change component (twoStep (piecesPerm d e) (seamPerm N)) (exposedEquiv N a) =
      component (twoStep (piecesPerm d e) (seamPerm N)) (exposedEquiv N b) ↔ _
  rw [h]
  constructor
  · rintro (h | h)
    · exact Or.inl ((exposedEquiv N).injective h)
    · exact Or.inr (by simpa only [composite, compositeMate,
        Equiv.symm_apply_apply] using congrArg (exposedEquiv N).symm h)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      apply (exposedEquiv N).symm.injective
      simpa only [composite, compositeMate, Equiv.symm_apply_apply] using h

def halfEdgeInternalComponent {N : ℕ} (d e : Matching (Boundary N)) :=
  {c : Component (halfEdgeStep d e) //
    ∀ a, component (halfEdgeStep d e) (outerPiece a) ≠ c}

instance {N : ℕ} (d e : Matching (Boundary N)) :
    Finite (halfEdgeInternalComponent d e) := by
  unfold halfEdgeInternalComponent
  infer_instance

def internalLoopCount {N : ℕ} (d e : Matching (Boundary N)) : ℕ :=
  Nat.card (halfEdgeInternalComponent d e)

def collapse {N : ℕ} : Piece N → GluingVertex N
  | (false,b) => upper b
  | (true,b) => lower b

def retain {N : ℕ} (x : GluingVertex N) : Piece N :=
  if x.1 = 0 then (false,(false,x.2))
  else if x.1 = 1 then (false,(true,x.2))
  else (true,(true,x.2))

theorem collapse_retain {N : ℕ} (x : GluingVertex N) : collapse (retain x) = x := by
  rcases x with ⟨l,i⟩
  fin_cases l <;> rfl

theorem retain_upper {N : ℕ} (a : Boundary N) : retain (upper a) = (false,a) := by
  rcases a with ⟨b,i⟩
  cases b <;> rfl

theorem collapse_seam {N : ℕ} (x : Piece N) : collapse (seamMate x) = collapse x := by
  rcases x with ⟨l,b,i⟩
  cases l <;> cases b <;> rfl

theorem retain_lower_path {N : ℕ} (d e : Matching (Boundary N)) (a : Boundary N) :
    Relation.EqvGen (halfEdgeStep d e) (retain (lower a)) (true,a) := by
  rcases a with ⟨b,i⟩
  cases b
  · exact .rel _ _ (Or.inr rfl)
  · exact .refl _

/-- Actual seam contraction identifies the half-edge execution graph with
the three-level multiplication graph defined before the first-return adapter. -/
def halfToTripleEquiv {N : ℕ} (d e : Matching (Boundary N)) :
    Component (halfEdgeStep d e) ≃ Component (gluingStep d e) := by
  apply contractionEquiv (halfEdgeStep d e) (gluingStep d e)
    collapse retain collapse_retain
  · intro x y h
    rcases h with h | h
    · subst y
      rcases x with ⟨l,b⟩
      cases l
      · exact .rel _ _ (Or.inl ⟨b,rfl,rfl⟩)
      · exact .rel _ _ (Or.inr ⟨b,rfl,rfl⟩)
    · subst y
      change Relation.EqvGen (gluingStep d e) (collapse x) (collapse (seamMate x))
      rw [collapse_seam]
      exact .refl _
  · intro x y h
    rcases h with ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩
    · rw [retain_upper, retain_upper]
      exact .rel _ _ (Or.inl rfl)
    · exact .trans _ _ _ (retain_lower_path d e a)
        (.trans _ _ _ (.rel _ _ (Or.inl rfl))
          (.symm _ _ (retain_lower_path d e (e.mate a))))
  · rintro ⟨l,b,i⟩
    cases l <;> cases b
    · exact .refl _
    · exact .refl _
    · exact .rel _ _ (Or.inr rfl)
    · exact .refl _

theorem halfToTriple_outer {N : ℕ} (d e : Matching (Boundary N)) (a : Boundary N) :
    halfToTripleEquiv d e (component (halfEdgeStep d e) (outerPiece a)) =
      component (gluingStep d e) (outer a) := by
  rcases a with ⟨b,i⟩
  cases b <;> rfl

theorem triple_component_iff {N : ℕ} (d e : Matching (Boundary N)) (a b : Boundary N) :
    component (gluingStep d e) (outer a) = component (gluingStep d e) (outer b) ↔
      b = a ∨ b = (composite d e).mate a := by
  rw [← halfToTriple_outer d e a, ← halfToTriple_outer d e b,
    (halfToTripleEquiv d e).injective.eq_iff]
  exact composite_component_iff d e a b

def internalComponentEquiv {N : ℕ} (d e : Matching (Boundary N)) :
    halfEdgeInternalComponent d e ≃ InternalComponent d e where
  toFun c := ⟨halfToTripleEquiv d e c.1,by
    intro a ha
    apply c.2 a
    apply (halfToTripleEquiv d e).injective
    rw [halfToTriple_outer]
    exact ha⟩
  invFun c := ⟨(halfToTripleEquiv d e).symm c.1,by
    intro a ha
    apply c.2 a
    rw [← halfToTriple_outer d e a, ha, Equiv.apply_symm_apply]⟩
  left_inv c := Subtype.ext ((halfToTripleEquiv d e).symm_apply_apply c.1)
  right_inv c := Subtype.ext ((halfToTripleEquiv d e).apply_symm_apply c.1)

theorem internalLoopCount_eq {N : ℕ} (d e : Matching (Boundary N)) :
    internalLoopCount d e = Nat.card (InternalComponent d e) :=
  Nat.card_congr (internalComponentEquiv d e)


end D5.S3.Topology.FiniteMatchingComposition
