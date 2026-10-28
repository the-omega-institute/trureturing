/- GID: D5/S3/Observer/Separation/CapacitySensitiveSupport
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/CapacitySensitiveSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Function.DependsOn]
   utility: none
   digest: Sensitive illegal cells determine exact fixed-tree protocol budgets. -/

import D5.S3.Observer.Separation.FixedTreeCommonExtension
import Mathlib.Logic.Function.DependsOn

/-! Least supports of finite-product costs and exact promised tree budgets. -/

set_option autoImplicit false

namespace D5.S3.Observer.Separation.CapacitySensitiveSupport

open D5.S3.Observer.Separation.FixedTreeCommonExtension
open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (capacity)

/-- A coordinate is sensitive when changing only it changes the result. -/
def sensitive {U : Type*} {O : U → Type*} {Y : Type*}
    (c : (∀ u, O u) → Y) : Set U :=
  {u | ∃ h h', (∀ j, j ≠ u → h j = h' j) ∧ c h ≠ c h'}

/-- For finite products, the sensitive coordinates are exactly the least support.
The value types and the result type can be infinite or empty. -/
theorem dependsOn_iff_sensitive_subset {U : Type*} [Finite U]
    {O : U → Type*} {Y : Type*} (c : (∀ u, O u) → Y) (S : Set U) :
    DependsOn c S ↔ sensitive c ⊆ S := by
  classical
  constructor
  · intro hs u hu
    by_contra huS
    obtain ⟨h, h', same, different⟩ := hu
    apply different
    apply hs
    intro j hj
    exact same j (fun e => huS (e ▸ hj))
  · intro hs
    let : Fintype U := Fintype.ofFinite U
    have chain (K : Finset U) : ∀ h h' : ∀ u, O u,
        (∀ u ∈ sensitive c, h u = h' u) →
        (∀ u ∉ K, h u = h' u) → c h = c h' := by
      induction K using Finset.induction_on with
      | empty =>
        intro h h' _ same
        exact congrArg c (funext (fun u => same u (by simp)))
      | @insert u K _ ih =>
        intro h h' same outside
        let z := Function.update h u (h' u)
        have first : c h = c z := by
          by_cases hu : u ∈ sensitive c
          · have eq : z = h := by
              simp only [z, ← same u hu, Function.update_eq_self]
            rw [eq]
          · by_contra different
            apply hu
            refine ⟨h, z, ?_, different⟩
            intro j hj
            simp [z, Function.update_of_ne hj]
        apply first.trans
        apply ih z h'
        · intro j hj
          by_cases hju : j = u
          · subst j; simp [z]
          · simpa [z, Function.update_of_ne hju] using same j hj
        · intro j hj
          by_cases hju : j = u
          · subst j; simp [z]
          · simpa [z, Function.update_of_ne hju] using
              outside j (by simp [hju, hj])
    intro h h' same
    exact chain Finset.univ h h' (fun u hu => same u (hs hu)) (by simp)

/-- The union of the sensitive scopes of all costs. -/
def jointSupport {U V O : Type*} (c : V → (U → O) → ℕ) : Set U :=
  {u | ∃ v, u ∈ sensitive (c v)}

/-- A local row is feasible when every extension of that row meets the bound. -/
def localFeasible {U V O : Type*} (c : V → (U → O) → ℕ)
    (k : ℕ) (v : V) : Set (sensitive (c v) → O) :=
  {s | ∀ h : U → O, (∀ u : sensitive (c v), h u.val = s u) → c v h ≤ k}

/-- Natural join on the union of the actual sensitive scopes. -/
def sensitiveJoin {U V O : Type*} (c : V → (U → O) → ℕ)
    (k : ℕ) : Set (jointSupport c → O) :=
  {s | ∀ v, (fun u : sensitive (c v) => s ⟨u.val, ⟨v, u.property⟩⟩) ∈
    localFeasible c k v}

private theorem feasible_iff_join {U V O : Type*} [Finite U] [Nonempty O]
    (c : V → (U → O) → ℕ) (k : ℕ) :
    (∃ h : U → O, ∀ v, c v h ≤ k) ↔ (sensitiveJoin c k).Nonempty := by
  classical
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨fun u => h u.val, ?_⟩
    intro v h' same
    have eq : c v h' = c v h :=
      (dependsOn_iff_sensitive_subset (c v) (sensitive (c v))).mpr
        (Set.Subset.refl _) (fun u hu => same ⟨u, hu⟩)
    exact eq.trans_le (hh v)
  · rintro ⟨s, hs⟩
    let h : U → O := fun u => if hu : u ∈ jointSupport c then s ⟨u, hu⟩
      else Classical.choice inferInstance
    refine ⟨h, fun v => hs v h ?_⟩
    intro u
    simp [h, show u.val ∈ jointSupport c from ⟨v, u.property⟩]

/-- Reconstruct a total task from its prescribed legal values and illegal cells. -/
noncomputable def complete {C O : Type*} (D : Set C) (f : D → O)
    (h : ↥(Dᶜ) → O) : C → O := by
  classical
  exact fun x => if hx : x ∈ D then f ⟨x, hx⟩ else h ⟨x, hx⟩

/-- Count the complete response rows reached by actual promised inputs.
The subtype in responseMessage only records membership in the full response image. -/
noncomputable def activeCapacity {I V O : Type} {X : I → Type}
    (D : Set (∀ i, X i)) (H : (∀ i, X i) → O) (s : Tree I V) : ℕ :=
  Nat.card (Set.range (fun x : D => responseMessage H s x.val))

/-- The original capacity functions, parameterized only by illegal cells. -/
noncomputable def sourceCost {I V O : Type} {X : I → Type}
    (t : Tree I V) (D : Set (∀ i, X i)) (f : D → O) :
    Nodes t → (↥(Dᶜ) → O) → ℕ :=
  fun v h => activeCapacity D (complete D f h) v.val

/-- The budget counts every original node, including the root. -/
def ProtocolBudget {I V O : Type} {X : I → Type}
    (t : Tree I V) (D : Set (∀ i, X i)) (f : D → O) (k : ℕ) : Prop :=
  ∃ (m : Implementation (V := V) X) (read : m.Message t → O),
    (∀ x : D, read (evaluate m t x.val) = f x) ∧
    ∀ v : Nodes t, reachable m D v.val ≤ k

/-- The least attainable original-node message budget. -/
noncomputable def minimumPeak {I V O : Type} {X : I → Type}
    (t : Tree I V) (D : Set (∀ i, X i)) (f : D → O) : ℕ :=
  sInf {k | ProtocolBudget t D f k}

/-- The least-support law and exact natural-join criterion for the original
finite-coordinate task and its complete fixed-tree protocols. -/
theorem source_result {I V O : Type} [Fintype I] {X : I → Type}
    [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (t : Tree I V) (ht : Full t) (hall : leaves t = Finset.univ)
    (D : Set (∀ i, X i)) (hD : D.Nonempty) (f : D → O) :
    (∀ (v : Nodes t) (S : Set ↥(Dᶜ)),
      DependsOn (sourceCost t D f v) S ↔ sensitive (sourceCost t D f v) ⊆ S) ∧
    (∀ k : ℕ, minimumPeak t D f ≤ k ↔ (sensitiveJoin (sourceCost t D f) k).Nonempty) := by
  classical
  let : Nonempty O := ⟨f ⟨hD.choose, hD.choose_spec⟩⟩
  have laws := D5.S3.Observer.Separation.FixedTreeCommonExtension.result t ht hall D hD f
  have budget_nonempty : ({k | ProtocolBudget t D f k} : Set ℕ).Nonempty := by
    obtain ⟨_, m, read, _, correct, _, _, _⟩ := laws.2.2.2.2.1
    refine ⟨Finset.univ.sup (protocolVector t D m), m, read, correct, ?_⟩
    intro v
    exact Finset.le_sup (f := protocolVector t D m) (Finset.mem_univ v)
  have budget_iff (k : ℕ) : minimumPeak t D f ≤ k ↔ ProtocolBudget t D f k := by
    constructor
    · intro hk
      obtain ⟨m, read, correct, bound⟩ :=
        (show ProtocolBudget t D f (minimumPeak t D f) from Nat.sInf_mem budget_nonempty)
      exact ⟨m, read, correct, fun v => (bound v).trans hk⟩
    · intro hk
      exact Nat.sInf_le hk
  have complete_correct (h : ↥(Dᶜ) → O) : ∀ x : D, complete D f h x.val = f x := by
    intro x
    simp [complete, x.property]
  have active_le (H : (∀ i, X i) → O) (v : Nodes t) :
      activeCapacity D H v.val ≤ capacity X H (fun i => i ∈ leaves v.val) := by
    apply Nat.card_le_card_of_injective
      (fun q : Set.range (fun x : D => responseMessage H v.val x.val) => q.val)
    exact fun _ _ he => Subtype.ext he
  constructor
  · intro v S
    exact dependsOn_iff_sensitive_subset (sourceCost t D f v) S
  · intro k
    rw [budget_iff k, ← feasible_iff_join (sourceCost t D f) k]
    constructor
    · rintro ⟨m, read, correct, bound⟩
      obtain ⟨H, hH, hb⟩ := laws.1 m read correct
      let h : ↥(Dᶜ) → O := fun u => H u.val
      refine ⟨h, ?_⟩
      have recover : complete D f h = H := by
        funext x
        by_cases hx : x ∈ D
        · simpa [complete, hx] using (hH ⟨x, hx⟩).symm
        · simp [complete, hx, h]
      intro v
      change activeCapacity D (complete D f h) v.val ≤ k
      rw [recover]
      exact (active_le H v).trans ((hb v).trans (bound v))
    · rintro ⟨h, hh⟩
      obtain ⟨read, correct, _, hr⟩ := laws.2.1 (complete D f h) (complete_correct h)
      refine ⟨canonical (complete D f h), read, correct, ?_⟩
      intro v
      have eq : reachable (canonical (complete D f h)) D v.val =
          sourceCost t D f v h := by
        unfold reachable sourceCost activeCapacity
        rw [hr v.val v.property]
        rfl
      exact eq.trans_le (hh v)

#print axioms dependsOn_iff_sensitive_subset
#print axioms source_result

end D5.S3.Observer.Separation.CapacitySensitiveSupport
