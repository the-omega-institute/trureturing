/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact finite-atomic or leafless classification on positive-drift forward regions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open NativePrefixIdentityReflection (gamma gamma_parent gamma_pair gamma_iterate
  gamma_positive atomicRank kappa kappa_iterate)
open NativeCompletionSupportClosure (embed_injective)

/-- Expressions after distributing fixed powers. A token shares its scalar name;
true selects a finite rank and false selects the divergent mode. -/
inductive Expr (k m : Nat) where
  | ground : Source → Expr k m
  | token : Fin k → Nat → Expr k m
  | var : Nat → Fin m → Expr k m
  | pair : Expr k m → Expr k m → Expr k m

variable {k m : Nat}

def value (mode : Fin k → Bool) (param : Fin k → Nat)
    (v : Fin m → CompletionTree) : Expr k m → CompletionTree
  | .ground t => embed t
  | .token j c => if mode j then atomic (param j + c) else Omega
  | .var a x => rho^[a] (v x)
  | .pair A B => node (value mode param v A) (value mode param v B)

abbrev System (k m : Nat) := List (Expr k m × Expr k m)

def Satisfies (E : System k m) (mode : Fin k → Bool) (param : Fin k → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ A B, (A, B) ∈ E → value mode param v A = value mode param v B

/-- Only mandatory positive equations generate exposed equalities. Both
orientations and every pair cancellation remain available simultaneously. -/
inductive Exposed (E : System k m) : Expr k m → Expr k m → Prop
  | original {A B} : (A, B) ∈ E → Exposed E A B
  | reverse {A B} : Exposed E A B → Exposed E B A
  | left {A B C D} : Exposed E (.pair A B) (.pair C D) → Exposed E A C
  | right {A B C D} : Exposed E (.pair A B) (.pair C D) → Exposed E B D

private theorem exposed_sound {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {A B : Expr k m} (h : Exposed E A B) : value mode param v A = value mode param v B := by
  induction h with
  | original h => exact sat _ _ h
  | reverse _ ih => exact ih.symm
  | left _ ih => exact (node_inj ih).1
  | right _ ih => exact (node_inj ih).2

inductive Occurs : Expr k m → Address → Nat → Fin m → Prop
  | var (a : Nat) (x : Fin m) : Occurs (.var a x) [] a x
  | left {A B p a x} : Occurs A p a x → Occurs (.pair A B) (false :: p) a x
  | right {A B p a x} : Occurs B p a x → Occurs (.pair A B) (true :: p) a x

private theorem occurrence_value (mode : Fin k → Bool) (param : Fin k → Nat)
    (v : Fin m → CompletionTree) {A : Expr k m} {p : Address} {a : Nat} {x : Fin m}
    (h : Occurs A p a x) : subtree p (value mode param v A) = some (rho^[a] (v x)) := by
  induction h with
  | var => rfl
  | left _ ih => exact ih
  | right _ ih => exact ih

/-- An edge retains its syntactic address and the original equation supplying it.
Original reach in the head residual is not assumed. -/
structure Edge (E : System k m) (x y : Fin m) where
  headPower : Nat
  occPower : Nat
  address : Address
  occurrence : ∃ A, Exposed E (.var headPower x) A ∧ Occurs A address occPower y

private theorem edge_present {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (e : Edge E x y) :
    subtree e.address (rho^[e.headPower] (v x)) = some (rho^[e.occPower] (v y)) := by
  obtain ⟨A, eq, occ⟩ := e.occurrence
  rw [show rho^[e.headPower] (v x) = value mode param v A from exposed_sound sat eq]
  exact occurrence_value mode param v occ

inductive Walk (E : System k m) : Fin m → Fin m → Type
  | nil (x : Fin m) : Walk E x x
  | snoc {x y z} : Walk E x y → Edge E y z → Walk E x z

namespace Walk

variable {E : System k m} {x y z : Fin m}

def append (p : Walk E x y) : {z : Fin m} → Walk E y z → Walk E x z
  | _, .nil _ => p
  | _, .snoc q e => .snoc (p.append q) e

def headSum : {x y : Fin m} → Walk E x y → Nat
  | _, _, .nil _ => 0
  | _, _, .snoc p e => p.headSum + e.headPower

def occSum : {x y : Fin m} → Walk E x y → Nat
  | _, _, .nil _ => 0
  | _, _, .snoc p e => p.occSum + e.occPower

/-- Each individual difference is taken in the integers, before summation. -/
def weight : {x y : Fin m} → Walk E x y → Int
  | _, _, .nil _ => 0
  | _, _, .snoc p e => p.weight + ((e.headPower : Int) - e.occPower)

def address : {x y : Fin m} → Walk E x y → Address
  | _, _, .nil _ => []
  | _, _, .snoc p e => p.address ++ e.address

def Strict : {x y : Fin m} → Walk E x y → Prop
  | _, _, .nil _ => False
  | _, _, .snoc p e => p.Strict ∨ e.address ≠ []

private theorem nil_append (p : Walk E x y) : (Walk.nil x).append p = p := by
  induction p with
  | nil => rfl
  | snoc p e ih => simp only [append, ih]

private theorem weight_eq (p : Walk E x y) : p.weight = (p.headSum : Int) - p.occSum := by
  induction p with
  | nil => simp [weight, headSum, occSum]
  | snoc p e ih => simp only [weight, headSum, occSum, Nat.cast_add, ih]; omega

end Walk

/-- Closed walks suffice; in particular, no simple cycle is excluded. -/
structure PositiveCycle (E : System k m) (root : Fin m) where
  walk : Walk E root root
  strict : walk.Strict
  positive : 0 < walk.weight

/-- A vertex of the chosen cycle is the endpoint of an actual prefix. -/
def CycleVertex {E : System k m} {root : Fin m} (c : PositiveCycle E root) (x : Fin m) : Prop :=
  ∃ p : Walk E root x, ∃ q : Walk E x root, p.append q = c.walk

/-- The union of forward reachability from every cycle vertex in the entire
exposed graph, including all definitions of a head. -/
def Region {E : System k m} {root : Fin m} (c : PositiveCycle E root) (y : Fin m) : Prop :=
  ∃ x, CycleVertex c x ∧ Nonempty (Walk E x y)

private theorem region_iff {E : System k m} {root y : Fin m} (c : PositiveCycle E root) :
    Region c y ↔ Nonempty (Walk E root y) := by
  constructor
  · rintro ⟨x, ⟨p, q, _⟩, ⟨r⟩⟩
    exact ⟨p.append r⟩
  · intro h
    exact ⟨root, ⟨.nil root, c.walk, Walk.nil_append _⟩, h⟩

private theorem root_in_region {E : System k m} {root : Fin m} (c : PositiveCycle E root) :
    Region c root := (region_iff c).mpr ⟨.nil root⟩

private theorem edge_finite {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (e : Edge E x y) (fin : IsFinite (v x)) : IsFinite (v y) :=
  (finite_iterate_iff e.occPower _).mp (finite_subtree e.address
    ((finite_iterate_iff e.headPower _).mpr fin) (edge_present sat e))

private theorem walk_finite {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (p : Walk E x y) (fin : IsFinite (v x)) : IsFinite (v y) := by
  induction p with
  | nil => exact fin
  | snoc p e ih => exact edge_finite sat e ih

private theorem subtree_mass (p : Address) (s t : Source)
    (present : subtree p (embed s) = some (embed t)) :
    gamma t ≤ gamma s ∧ (p ≠ [] → 0 < gamma t → gamma t < gamma s) := by
  induction p generalizing s with
  | nil =>
    have h : s = t := embed_injective (Option.some.inj present)
    subst s
    exact ⟨le_rfl, fun h => False.elim (h rfl)⟩
  | cons b p ih =>
    cases s with
    | of a => simp [embed, subtree, leaf] at present
    | mul l r =>
      cases b
      · obtain ⟨h, _⟩ := ih l present
        refine ⟨h.trans (gamma_parent l r).1, ?_⟩
        intro _ pos
        rw [gamma_pair l r (Or.inl (lt_of_lt_of_le pos h))]
        omega
      · obtain ⟨h, _⟩ := ih r present
        refine ⟨h.trans (gamma_parent l r).2, ?_⟩
        intro _ pos
        rw [gamma_pair l r (Or.inr (lt_of_lt_of_le pos h))]
        omega

private theorem edge_mass {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (e : Edge E x y) (s t : Source) (hs : embed s = v x) (ht : embed t = v y) :
    gamma t ≤ gamma s ∧ (e.address ≠ [] → 0 < gamma t → gamma t < gamma s) := by
  have present := edge_present sat e
  rw [← hs, ← ht, iterate_embed, iterate_embed] at present
  simpa only [gamma_iterate] using subtree_mass e.address _ _ present

private theorem walk_mass {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (p : Walk E x y) (s t : Source) (hs : embed s = v x) (ht : embed t = v y) :
    gamma t ≤ gamma s ∧ (p.Strict → 0 < gamma t → gamma t < gamma s) := by
  induction p generalizing t with
  | nil =>
    have eq : s = t := embed_injective (hs.trans ht.symm)
    subst t
    refine ⟨le_rfl, ?_⟩
    simp only [Walk.Strict, false_implies]
  | snoc p e ih =>
    obtain ⟨u, hu⟩ := walk_finite sat p ⟨s, hs⟩
    obtain ⟨hp, hps⟩ := ih u hu
    obtain ⟨he, hes⟩ := edge_mass sat e u t hu ht
    refine ⟨he.trans hp, ?_⟩
    simp only [Walk.Strict]
    rintro (strict | strict) pos
    · exact lt_of_le_of_lt he (hps strict (lt_of_lt_of_le pos he))
    · exact lt_of_lt_of_le (hes strict pos) hp

private theorem subtree_append (p q : Address) (X : CompletionTree) :
    subtree (p ++ q) X = (subtree p X).bind (subtree q) := by
  induction p generalizing X with
  | nil => rfl
  | cons b p ih =>
    induction X using tree_cases with
    | leaf_case a => simp [subtree, leaf]
    | node_case l r => cases b <;> exact ih _

/-- The endpoint is a subtree of the one original head tree, with the same
accumulated address and both cumulative powers. -/
private theorem walk_infinite_transport {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (p : Walk E x y) (inf : ¬ IsFinite (v y)) :
    ∃ U, subtree p.address (v x) = some U ∧ ¬ IsFinite U ∧
      rho^[p.headSum] U = rho^[p.occSum] (v y) := by
  induction p with
  | nil =>
    exact ⟨v x, by simp [Walk.address, subtree], inf, by simp [Walk.headSum, Walk.occSum]⟩
  | @snoc y z p e ih =>
    obtain ⟨U, original, _, eq⟩ := ih (fun h => inf (edge_finite sat e h))
    have transported := original_subtree_transport p.occSum e.address
      (rho^[e.headPower] (v y)) (rho^[e.occPower] (v z)) (edge_present sat e)
    have power_eq : rho^[p.headSum + e.headPower] U =
        rho^[p.occSum] (rho^[e.headPower] (v y)) := by
      rw [Nat.add_comm p.headSum e.headPower, Function.iterate_add_apply, eq]
      exact Function.Commute.iterate_iterate_self rho e.headPower p.occSum _
    have endpoint : subtree e.address (rho^[p.headSum + e.headPower] U) =
        some (rho^[p.occSum + e.occPower] (v z)) := by
      rw [power_eq, Function.iterate_add_apply]
      exact transported
    obtain ⟨W, actual, relation, infW⟩ := infinite_subtree_origin
      (p.headSum + e.headPower) e.address U _ endpoint
      (fun h => inf ((finite_iterate_iff (p.occSum + e.occPower) _).mp h))
    refine ⟨W, ?_, infW, ?_⟩
    · simp only [Walk.address]
      rw [subtree_append, original]
      exact actual
    · simpa only [Walk.headSum, Walk.occSum] using relation


namespace Walk

variable {E : System k m} {x y z : Fin m}

private theorem append_data (p : Walk E x y) (q : Walk E y z) :
    (p.append q).headSum = p.headSum + q.headSum ∧
    (p.append q).occSum = p.occSum + q.occSum ∧
    (p.append q).address = p.address ++ q.address := by
  induction q with
  | nil => simp [append, headSum, occSum, address]
  | snoc q e ih =>
    simp only [append, headSum, occSum, address, ih.1, ih.2.1, ih.2.2,
      Nat.add_assoc, List.append_assoc, and_self]

def repeated (p : Walk E x x) : Nat → Walk E x x
  | 0 => .nil x
  | n+1 => (p.repeated n).append p

end Walk

def repeatedAddress (p : Address) : Nat → Address
  | 0 => []
  | n+1 => repeatedAddress p n ++ p

private theorem repeat_data {E : System k m} {x : Fin m} (p : Walk E x x) (n : Nat) :
    (p.repeated n).headSum = n * p.headSum ∧
    (p.repeated n).occSum = n * p.occSum ∧
    (p.repeated n).address = repeatedAddress p.address n := by
  induction n with
  | zero => simp [Walk.repeated, Walk.headSum, Walk.occSum, Walk.address, repeatedAddress]
  | succ n ih =>
    obtain ⟨ha, hb, hp⟩ := Walk.append_data (p.repeated n) p
    simp only [Walk.repeated, ha, hb, hp, ih.1, ih.2.1, ih.2.2, Nat.succ_mul,
      repeatedAddress, and_self]

private theorem drift_positive {E : System k m} {root : Fin m} (c : PositiveCycle E root) :
    c.walk.occSum < c.walk.headSum := by
  have h := c.positive
  rw [Walk.weight_eq] at h
  omega

private theorem cycle_preimages {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {root : Fin m} (c : PositiveCycle E root) (inf : ¬ IsFinite (v root)) (n : Nat) :
    ∃ U, subtree (repeatedAddress c.walk.address n) (v root) = some U ∧ ¬ IsFinite U ∧
      v root = rho^[n * (c.walk.headSum - c.walk.occSum)] U := by
  obtain ⟨U, original, infU, relation⟩ := walk_infinite_transport sat (c.walk.repeated n) inf
  obtain ⟨ha, hb, hp⟩ := repeat_data c.walk n
  rw [ha, hb] at relation
  rw [hp] at original
  refine ⟨U, original, infU, ?_⟩
  apply rho_injective.iterate (n * c.walk.occSum)
  rw [← Function.iterate_add_apply, ← Nat.mul_add,
    Nat.add_sub_of_le (Nat.le_of_lt (drift_positive c))]
  exact relation.symm

private theorem cycle_infinite_omega {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {root : Fin m} (c : PositiveCycle E root) (inf : ¬ IsFinite (v root)) : v root = Omega := by
  apply eq_omega_of_full
  intro n
  obtain ⟨U, _, _, back⟩ := cycle_preimages sat c inf (2*n)
  have pos : 0 < c.walk.headSum - c.walk.occSum := by have := drift_positive c; omega
  have bound := Nat.le_mul_of_pos_right (2*n) pos
  rw [back, show 2*n*(c.walk.headSum-c.walk.occSum) =
      2*n + (2*n*(c.walk.headSum-c.walk.occSum)-2*n) by omega,
    Function.iterate_add_apply]
  exact iterate_full n _

private theorem subtree_omega (p : Address) : subtree p Omega = some Omega := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    conv_lhs => rw [omega_node]
    cases b <;> exact ih

private theorem edge_omega {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (e : Edge E x y) (h : v x = Omega) : v y = Omega := by
  have present := edge_present sat e
  rw [h, iterate_omega, subtree_omega] at present
  apply rho_injective.iterate e.occPower
  rw [iterate_omega]
  exact (Option.some.inj present).symm

private theorem walk_omega {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {x y : Fin m} (p : Walk E x y) (h : v x = Omega) : v y = Omega := by
  induction p with
  | nil => exact h
  | snoc p e ih => exact edge_omega sat e ih

private theorem zero_mass_atomic (t : Source) (zero : gamma t = 0) :
    ∃ q : Nat, embed t = atomic q := by
  cases rank : atomicRank t with
  | none => have := (gamma_positive t).mpr rank; omega
  | some q =>
    refine ⟨q, ?_⟩
    have ht := atomicRank_sound t q rank
    change embed t = rho^[q] (embed (.of true))
    rw [iterate_embed, ht]

private theorem finite_region_values {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {root : Fin m} (c : PositiveCycle E root) (fin : IsFinite (v root)) :
    ∀ x : {x // Region c x}, ∃ q : Nat, v x = atomic q := by
  obtain ⟨t, ht⟩ := fin
  have zero : gamma t = 0 := by
    have strict := (walk_mass sat c.walk t t ht ht).2 c.strict
    omega
  intro x
  obtain ⟨p⟩ := (region_iff c).mp x.property
  obtain ⟨s, hs⟩ := walk_finite sat p ⟨t, ht⟩
  have mass := (walk_mass sat p t s ht hs).1
  obtain ⟨q, hq⟩ := zero_mass_atomic s (by omega)
  exact ⟨q, hs.symm.trans hq⟩

private theorem infinite_region_values {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {v : Fin m → CompletionTree} (sat : Satisfies E mode param v)
    {root : Fin m} (c : PositiveCycle E root) (inf : ¬ IsFinite (v root)) :
    ∀ x, Region c x → v x = Omega := by
  intro x hx
  obtain ⟨p⟩ := (region_iff c).mp hx
  exact walk_omega sat p (cycle_infinite_omega sat c inf)

private theorem atomic_injective : Function.Injective atomic := by
  intro a b h
  apply NativeRankedEqualityCompiler.atomic_injective
  apply embed_injective
  simpa only [atomic, show leaf true = embed (.of true) from rfl, iterate_embed] using h

private theorem atomic_finite (q : Nat) : IsFinite (atomic q) :=
  ⟨substitution^[q] (.of true), (iterate_embed q (.of true)).symm⟩

private theorem omega_not_finite : ¬ IsFinite Omega := by
  rintro ⟨t, ht⟩
  have eq : substitution t = t := embed_injective (by rw [← rho_embed, ht, rho_omega])
  have clock := congrArg kappa eq
  have step := kappa_iterate 1 t
  change kappa (substitution t) = kappa t + 1 at step
  omega

/-- Natural ranks are assigned only to the region. All other coordinates retain
their exact original values. -/
noncomputable def finiteReplace {E : System k m} {root : Fin m} (c : PositiveCycle E root)
    (q : {x // Region c x} → Nat) (v : Fin m → CompletionTree) : Fin m → CompletionTree := by
  classical
  exact fun x => if h : Region c x then atomic (q ⟨x, h⟩) else v x

noncomputable def infiniteReplace {E : System k m} {root : Fin m} (c : PositiveCycle E root)
    (v : Fin m → CompletionTree) : Fin m → CompletionTree := by
  classical
  exact fun x => if Region c x then Omega else v x

/-- Extra predicates retain their original types via their captured parameters.
They may include scalar guards, reconstructions, mixed completed comparisons,
and predicates on the original finite-source charts. -/
def Solution (E : System k m) (mode : Fin k → Bool) (param : Fin k → Nat)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree) : Prop :=
  Satisfies E mode param v ∧ extra v

def FiniteAlternative {E : System k m} {root : Fin m} (c : PositiveCycle E root)
    (mode : Fin k → Bool) (param : Fin k → Nat)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree) : Prop :=
  ∃! q : {x // Region c x} → Nat,
    v = finiteReplace c q v ∧ Solution E mode param extra (finiteReplace c q v)

def InfiniteAlternative {E : System k m} {root : Fin m} (c : PositiveCycle E root)
    (mode : Fin k → Bool) (param : Fin k → Nat)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree) : Prop :=
  v = infiniteReplace c v ∧ Solution E mode param extra (infiniteReplace c v)

private theorem finite_alternative {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {extra : (Fin m → CompletionTree) → Prop}
    {v : Fin m → CompletionTree} (sol : Solution E mode param extra v)
    {root : Fin m} (c : PositiveCycle E root) (fin : IsFinite (v root)) :
    FiniteAlternative c mode param extra v := by
  classical
  choose q hq using finite_region_values sol.1 c fin
  have reconstruct : v = finiteReplace c q v := by
    funext x
    by_cases hx : Region c x
    · simpa only [finiteReplace, dif_pos hx] using hq ⟨x, hx⟩
    · simp only [finiteReplace, dif_neg hx]
  refine ⟨q, ⟨reconstruct, ?_⟩, ?_⟩
  · rwa [← reconstruct]
  · intro q' hq'
    funext x
    apply atomic_injective
    have at_x := congrFun hq'.1 x.val
    simp only [finiteReplace, dif_pos x.property] at at_x
    exact at_x.symm.trans (hq x)

private theorem infinite_alternative {E : System k m} {mode : Fin k → Bool}
    {param : Fin k → Nat} {extra : (Fin m → CompletionTree) → Prop}
    {v : Fin m → CompletionTree} (sol : Solution E mode param extra v)
    {root : Fin m} (c : PositiveCycle E root) (inf : ¬ IsFinite (v root)) :
    InfiniteAlternative c mode param extra v := by
  classical
  have values := infinite_region_values sol.1 c inf
  have reconstruct : v = infiniteReplace c v := by
    funext x
    by_cases hx : Region c x
    · simpa only [infiniteReplace, if_pos hx] using values x hx
    · simp only [infiniteReplace, if_neg hx]
  exact ⟨reconstruct, reconstruct ▸ sol⟩

private theorem alternatives_disjoint {E : System k m} {root : Fin m}
    (c : PositiveCycle E root) (mode : Fin k → Bool) (param : Fin k → Nat)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree) :
    ¬ (FiniteAlternative c mode param extra v ∧ InfiniteAlternative c mode param extra v) := by
  classical
  rintro ⟨⟨q, ⟨finiteEq, _⟩, _⟩, infiniteEq, _⟩
  have hf := congrFun finiteEq root
  have hi := congrFun infiniteEq root
  simp only [finiteReplace, dif_pos (root_in_region c)] at hf
  simp only [infiniteReplace, if_pos (root_in_region c)] at hi
  have eq : atomic (q ⟨root, root_in_region c⟩) = Omega := hf.symm.trans hi
  exact omega_not_finite (eq ▸ atomic_finite _)

/-- Every positive-drift strict cycle gives two disjoint exact substitution
systems on its entire forward region. Finite ranks are unique natural numbers;
all original equations and extra predicates remain in both systems. -/
theorem positive_drift_region_split (E : System k m) (mode : Fin k → Bool)
    (param : Fin k → Nat) (root : Fin m) (c : PositiveCycle E root)
    (extra : (Fin m → CompletionTree) → Prop) (v : Fin m → CompletionTree) :
    (Solution E mode param extra v ↔
      FiniteAlternative c mode param extra v ∨ InfiniteAlternative c mode param extra v) ∧
    ¬ (FiniteAlternative c mode param extra v ∧ InfiniteAlternative c mode param extra v) := by
  classical
  refine ⟨?_, alternatives_disjoint c mode param extra v⟩
  constructor
  · intro sol
    by_cases fin : IsFinite (v root)
    · exact Or.inl (finite_alternative sol c fin)
    · exact Or.inr (infinite_alternative sol c fin)
  · rintro (⟨q, ⟨reconstruct, sol⟩, _⟩ | ⟨reconstruct, sol⟩)
    · exact reconstruct.symm ▸ sol
    · exact reconstruct.symm ▸ sol

end D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion
