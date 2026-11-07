/- GID: D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.claim; result=D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result; claim=D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.claim
   digest: Refutes least omega-chain-partitionable extensions using a fork and two incompatible models. -/

/- result: proof_shape: bind-only; escape_witness: none.
   admission_basis: open-problem-resolution (#23817; Refuted)
   Direct frozen dependencies: none (all declarations).
   Private theorems, each proof_shape: bind-only; escape_witness: none:
     omega_successor -> incompatible; rays_upper_comparable -> incompatible;
     tail_forced_bound -> incompatible; partition_of_two -> rays_partition, tail_partition;
     rays_partition -> result; tail_partition -> result; incompatible -> result.
   Proposition-valued private definitions are classified as bind-only:
     rayLe -> rayOrder, intoRays; tailLe -> tailOrder, intoTail, tail_forced_bound.
   Definitions: IsOmegaChain, OmegaPartitionable, IsExtension, claim, Fork, forkOrder,
     Rays, rayLe, rayOrder, Tail, tailLe, tailOrder, forkRay, intoRays, forkTail,
     intoTail, rayEmbed, evenEmbed, oddEmbed.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   The source definitions and Question 2.32 quotation are recorded in the Scribe and
   Library note for arXiv:2610.29056v1. The public claim keeps the source's literal
   partition and induced-order conventions; the proof uses the displayed constructions. -/

import Mathlib.Order.Hom.Basic
import Mathlib.Order.Setoid.Partition
import Mathlib.Order.Hom.Set
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisOmegaChainExtensionRefutation

/-- A part with its inherited order is order-isomorphic to the ordinal omega. -/
def IsOmegaChain {P : Type} [PartialOrder P] (C : Set P) : Prop :=
  Nonempty (ℕ ≃o C)

/-- The parts form a partition of the entire poset, and every part is an omega-chain. -/
def OmegaPartitionable (P : Type) [PartialOrder P] : Prop :=
  ∃ D : Set (Set P), Setoid.IsPartition D ∧ ∀ C : Set P, C ∈ D → IsOmegaChain C

/-- An extension retains the induced order of the original poset. -/
def IsExtension (P Q : Type) [PartialOrder P] [PartialOrder Q] : Prop :=
  Nonempty (P ↪o Q)

/-- Question 2.32: every poset has an omega-chain-partitionable extension
that order-embeds into every omega-chain-partitionable extension of that poset.
No comparison embedding is required to fix the original poset. -/
def claim : Prop :=
  ∀ (P : Type) (pOrder : PartialOrder P),
    ∃ (Q : Type) (qOrder : PartialOrder Q),
      @IsExtension P Q pOrder qOrder ∧ @OmegaPartitionable Q qOrder ∧
        ∀ (Q' : Type) (qOrder' : PartialOrder Q'),
          @IsExtension P Q' pOrder qOrder' → @OmegaPartitionable Q' qOrder' →
            Nonempty (@OrderEmbedding Q Q' qOrder.toLE qOrder'.toLE)

private theorem omega_successor {Q : Type} [PartialOrder Q]
    (hQ : OmegaPartitionable Q) (x : Q) : ∃ z : Q, x < z := by
  obtain ⟨D, hD, hC⟩ := hQ
  obtain ⟨C, hx, _⟩ := hD.2 x
  obtain ⟨e⟩ := hC C hx.1
  let n := e.symm ⟨x, hx.2⟩
  refine ⟨(e (n + 1)).val, ?_⟩
  have h := e.strictMono (Nat.lt_succ_self n)
  have hn : e n = ⟨x, hx.2⟩ := e.apply_symm_apply _
  rw [hn] at h
  exact h

private inductive Fork
  | root | left | right
  deriving DecidableEq

private instance forkOrder : PartialOrder Fork where
  le x y := x = .root ∨ x = y
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h | rfl
    · exact Or.inl h
    · exact hyz
  le_antisymm x y hxy hyx := by
    rcases hxy with h | h
    · rcases hyx with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

private def Rays := Bool × ℕ

private def rayLe (x y : Rays) : Prop :=
  x = (false, 0) ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

private instance rayOrder : PartialOrder Rays where
  le := rayLe
  le_refl x := Or.inr ⟨rfl, le_rfl⟩
  le_trans x y z hxy hyz := by
    rcases hxy with h | ⟨h1,h2⟩
    · exact Or.inl h
    · rcases hyz with h | ⟨h3,h4⟩
      · subst y
        left
        apply Prod.ext
        · exact h1
        · dsimp at h2; omega
      · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
  le_antisymm x y hxy hyx := by
    rcases hxy with h | ⟨h1,h2⟩
    · subst x
      rcases hyx with h | ⟨h1,h2⟩
      · exact h.symm
      · apply Prod.ext
        · exact h1.symm
        · dsimp at h2; omega
    · rcases hyx with h | ⟨h3,h4⟩
      · subst y
        apply Prod.ext
        · exact h1
        · dsimp at h2; omega
      · exact Prod.ext h1 (le_antisymm h2 h4)

private def Tail := ℕ

private def tailLe (x y : Tail) : Prop :=
  (show ℕ from x) ≤ (show ℕ from y) ∧
    ¬ (x = (show Tail from (1 : ℕ)) ∧ y = (show Tail from (2 : ℕ)))

private instance tailOrder : PartialOrder Tail where
  le := tailLe
  le_refl x := by dsimp [tailLe, Tail]; omega
  le_trans x y z hxy hyz := by dsimp [tailLe, Tail] at *; omega
  le_antisymm x y hxy hyx := Nat.le_antisymm hxy.1 hyx.1

private def forkRay : Fork → Rays
  | .root => (false, 0)
  | .left => (false, 1)
  | .right => (true, 0)

private def intoRays : Fork ↪o Rays where
  toFun := forkRay
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [forkRay, Rays]
  map_rel_iff' := by
    intro x y
    change rayLe (forkRay x) (forkRay y) ↔ (x = .root ∨ x = y)
    cases x <;> cases y <;> simp [forkRay, rayLe, Rays]

private def forkTail : Fork → Tail
  | .root => (0 : ℕ)
  | .left => (1 : ℕ)
  | .right => (2 : ℕ)

private def intoTail : Fork ↪o Tail where
  toFun := forkTail
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [forkTail, Tail]
  map_rel_iff' := by
    intro x y
    change tailLe (forkTail x) (forkTail y) ↔ (x = .root ∨ x = y)
    cases x <;> cases y <;> simp [forkTail, tailLe, Tail]

private theorem rays_upper_comparable (x y z : Rays)
    (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  rcases hx with h | ⟨h1, h2⟩
  · exact Or.inl (Or.inl h)
  rcases hy with h | ⟨h3, h4⟩
  · exact Or.inr (Or.inl h)
  rcases le_total x.2 y.2 with h | h
  · exact Or.inl (Or.inr ⟨h1.trans h3.symm, h⟩)
  · exact Or.inr (Or.inr ⟨h3.trans h1.symm, h⟩)

private theorem tail_forced_bound (x y z : Tail)
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) (hxz : x < z) : y ≤ z := by
  change ¬ tailLe x y at hxy
  change ¬ tailLe y x at hyx
  change tailLe x z ∧ ¬ tailLe z x at hxz
  change tailLe y z
  dsimp [tailLe, Tail] at *
  omega

private theorem partition_of_two {X : Type} [PartialOrder X]
    (e₀ e₁ : ℕ ↪o X)
    (cover : ∀ x : X, x ∈ Set.range e₀ ∨ x ∈ Set.range e₁)
    (disjoint : ∀ x : X, x ∈ Set.range e₀ → x ∈ Set.range e₁ → False) :
    OmegaPartitionable X := by
  refine ⟨{Set.range e₀, Set.range e₁}, ?_, ?_⟩
  · constructor
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · have hm : e₀ 0 ∈ Set.range e₀ := Set.mem_range_self 0
        rw [← h] at hm
        exact hm
      · have hm : e₁ 0 ∈ Set.range e₁ := Set.mem_range_self 0
        rw [← h] at hm
        exact hm
    · intro x
      rcases cover x with hx | hx
      · refine ⟨Set.range e₀, ⟨by simp, hx⟩, ?_⟩
        intro C hC
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
        rcases hC.1 with h | h
        · exact h
        · exact False.elim (disjoint x hx (h ▸ hC.2))
      · refine ⟨Set.range e₁, ⟨by simp, hx⟩, ?_⟩
        intro C hC
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
        rcases hC.1 with h | h
        · exact False.elim (disjoint x (h ▸ hC.2) hx)
        · exact h
  · intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact ⟨e₀.orderIso⟩
    · exact ⟨e₁.orderIso⟩

private def rayEmbed (b : Bool) : ℕ ↪o Rays where
  toFun n := (b, n)
  inj' := by intro n m h; exact congrArg Prod.snd h
  map_rel_iff' := by
    intro n m
    change ((b, n) = (false, 0) ∨ (b = b ∧ n ≤ m)) ↔ n ≤ m
    simp only [Prod.mk.injEq, true_and]
    omega

private theorem rays_partition : OmegaPartitionable Rays := by
  apply partition_of_two (rayEmbed false) (rayEmbed true)
  · rintro ⟨b, n⟩
    cases b
    · exact Or.inl ⟨n, rfl⟩
    · exact Or.inr ⟨n, rfl⟩
  · intro x hx hy
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    have h := congrArg Prod.fst hm
    simp [rayEmbed] at h

private def evenEmbed : ℕ ↪o Tail where
  toFun n := 2 * n
  inj' := by intro n m h; change (2 * n : ℕ) = 2 * m at h; omega
  map_rel_iff' := by
    intro n m
    change (2 * n ≤ 2 * m ∧ ¬ (2 * n = 1 ∧ 2 * m = 2)) ↔ n ≤ m
    omega

private def oddEmbed : ℕ ↪o Tail where
  toFun n := 2 * n + 1
  inj' := by intro n m h; change (2 * n + 1 : ℕ) = 2 * m + 1 at h; omega
  map_rel_iff' := by
    intro n m
    change (2 * n + 1 ≤ 2 * m + 1 ∧ ¬ (2 * n + 1 = 1 ∧ 2 * m + 1 = 2)) ↔ n ≤ m
    omega

private theorem tail_partition : OmegaPartitionable Tail := by
  apply partition_of_two evenEmbed oddEmbed
  · intro x
    let n : ℕ := x
    by_cases h : n % 2 = 0
    · left; refine ⟨n / 2, ?_⟩; change 2 * (n / 2) = n; omega
    · right; refine ⟨n / 2, ?_⟩; change 2 * (n / 2) + 1 = n; omega
  · intro x hx hy
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    change 2 * m + 1 = 2 * n at hm
    omega

private theorem incompatible {Q : Type} [PartialOrder Q]
    (hQ : OmegaPartitionable Q) (p : Fork ↪o Q)
    (f : Q ↪o Rays) (g : Q ↪o Tail) : False := by
  have hab : ¬ p .left ≤ p .right := by
    intro h
    have h' := p.le_iff_le.mp h
    change Fork.left = .root ∨ Fork.left = .right at h'
    simpa using h'
  have hba : ¬ p .right ≤ p .left := by
    intro h
    have h' := p.le_iff_le.mp h
    change Fork.right = .root ∨ Fork.right = .left at h'
    simpa using h'
  obtain ⟨z, hz⟩ := omega_successor hQ (p .left)
  have hbz : p .right ≤ z := by
    apply g.le_iff_le.mp
    apply tail_forced_bound (g (p .left)) (g (p .right)) (g z)
    · exact fun h => hab (g.le_iff_le.mp h)
    · exact fun h => hba (g.le_iff_le.mp h)
    · exact g.strictMono hz
  rcases rays_upper_comparable (f (p .left)) (f (p .right)) (f z)
      (f.monotone hz.le) (f.monotone hbz) with h | h
  · exact hab (f.le_iff_le.mp h)
  · exact hba (f.le_iff_le.mp h)

theorem result : ¬ claim := by
  intro h
  obtain ⟨Q, qOrder, hp, hQ, hleast⟩ := h Fork forkOrder
  letI := qOrder
  obtain ⟨p⟩ := hp
  obtain ⟨f⟩ := hleast Rays rayOrder ⟨intoRays⟩ rays_partition
  obtain ⟨g⟩ := hleast Tail tailOrder ⟨intoTail⟩ tail_partition
  exact incompatible hQ p f g

end D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisOmegaChainExtensionRefutation
