/- GID: D5/S0/Certificates/Algebra/WangConjecture53Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/WangConjecture53Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Defs, mathlib/module/Mathlib.GroupTheory.Congruence.Defs, mathlib/module/Mathlib.Data.ENat.Lattice]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim; result=D5/S0/Certificates/Algebra/WangConjecture53Refutation.result; claim=D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim
   digest: A six-element ordinary rational semigroup algebra refutes Wang's Conjecture 5.3. -/

/- admission_basis: open-problem-resolution (issue #23871)
   Private helpers are consumed by the designated refutation result.
   No contracted semigroup algebra is used. -/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Tactic

/-! # An ordinary semigroup-algebra counterexample to Wang Conjecture 5.3 -/

namespace D5.S0.Certificates.Algebra.WangConjecture53Refutation

noncomputable section

/-- Index n denotes the positive multiple (n+1)a, without adjoining an identity. -/
def positiveMultiple {S : Type*} [Add S] (a : S) : ℕ → S
  | 0 => a
  | n + 1 => positiveMultiple a n + a

/-- The positive cyclic subsemigroup, including no artificial zeroth multiple. -/
def cyclic {S : Type*} [Add S] (a : S) : Set S := Set.range (positiveMultiple a)

/-- The source's cyclic idempotent specification. -/
def IsCyclicIdempotent {S : Type*} [Add S] (a e : S) : Prop :=
  e ∈ cyclic a ∧ e + e = e

/-- Choose the cyclic idempotent; the fallback is irrelevant whenever one exists. -/
def cyclicIdempotent {S : Type*} [Add S] (a : S) : S := by
  classical
  exact if h : ∃ e, IsCyclicIdempotent a e then h.choose else a

/-- Being a group with an identity in the positive cyclic subsemigroup itself. -/
def CyclicIsGroup {S : Type*} [Add S] (a : S) : Prop :=
  ∃ e ∈ cyclic a, (∀ x ∈ cyclic a, e + x = x) ∧
    ∀ x ∈ cyclic a, ∃ y ∈ cyclic a, x + y = e

/-- Least positive eventual shift of the positive multiples: the cyclic period. -/
def period {S : Type*} [Add S] (a : S) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ k, ∀ m, k ≤ m →
    positiveMultiple a (m + n) = positiveMultiple a m}

/-- LCM of cyclic periods, rather than cyclic indices or sizes. -/
def semigroupExponent (S : Type*) [Add S] [Finite S] : ℕ := by
  letI := Fintype.ofFinite S
  exact Finset.univ.lcm (period (S := S))

/-- The paper's root-count definition; encard also distinguishes infinite root sets. -/
def Splitting (S K : Type*) [Add S] [Finite S] [Field K] : Prop :=
  {z : K | z ^ semigroupExponent S = 1}.encard = semigroupExponent S

/-- Both source admissibility alternatives, with no characteristic restriction in (i). -/
def Admissible (S K : Type*) [Add S] [Finite S] [Field K] : Prop :=
  Splitting S K ∨ ∃ p k : ℕ, p.Prime ∧ CharP K p ∧ semigroupExponent S = p ^ k

/-- The ordinary semigroup-algebra factor; every semigroup label is retained. -/
def factor {S K : Type*} [AddCommSemigroup S] [Field K] (s : S) (a : K) :
    AddMonoidAlgebra K S :=
  AddMonoidAlgebra.single s 1 - AddMonoidAlgebra.single (cyclicIdempotent s) a

/-- Positive products do not presume that a general semigroup algebra has a unit.
The empty branch is unused for positive lengths; zero is included separately in d. -/
def factorProduct {S K : Type*} [AddCommSemigroup S] [Field K] :
    List S → (ℕ → K) → AddMonoidAlgebra K S
  | [], _ => 0
  | [s], c => factor s (c 0)
  | s :: t :: l, c => factor s (c 0) * factorProduct (t :: l) (fun i => c (i+1))

/-- Independently nonzero coefficients at exactly the positions of the sequence.
Values outside this finite prefix do not occur in the product. -/
def GoodSequence {S K : Type*} [AddCommSemigroup S] [Field K] (l : List S) : Prop :=
  ∀ c : ℕ → K, (∀ i, i < l.length → c i ≠ 0) → factorProduct l c ≠ 0

/-- Supremum of admissible finite lengths in ENat. Infinity means unboundedness,
not a finite sequence or an asserted infinite product. Adding zero changes no supremum. -/
def algebraicD (S K : Type*) [AddCommSemigroup S] [Field K] : ℕ∞ :=
  ⨆ (l : List S) (_ : GoodSequence (K := K) l), (l.length : ℕ∞)

/-- Principal ideal membership, with the element itself even without an identity. -/
def Below {S : Type*} [Add S] (x a : S) : Prop := x = a ∨ ∃ c, x = a + c

/-- Green H is equality of principal ideals. -/
def Green {S : Type*} [Add S] (a b : S) : Prop := ∀ x, Below x a ↔ Below x b

private theorem below_trans {S : Type*} [AddSemigroup S] {x a b : S}
    (h : Below x a) (g : Below a b) : Below x b := by
  rcases h with rfl | ⟨c, rfl⟩
  · exact g
  · rcases g with rfl | ⟨d, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
    · exact Or.inr ⟨d+c, add_assoc _ _ _⟩

private theorem green_add_right {S : Type*} [AddCommSemigroup S] {a b : S}
    (h : Green a b) (c : S) : Green (a+c) (b+c) := by
  have hab : Below a b := (h a).mp (Or.inl rfl)
  have hba : Below b a := (h b).mpr (Or.inl rfl)
  have step {x y : S} (hxy : Below x y) : Below (x+c) (y+c) := by
    rcases hxy with rfl | ⟨d, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨d, by ac_rfl⟩
  intro x
  exact ⟨fun hx => below_trans hx (step hab), fun hx => below_trans hx (step hba)⟩

/-- The actual Green congruence, not a numerical proxy. -/
def greenCon (S : Type*) [AddCommSemigroup S] : AddCon S where
  r := Green
  iseqv := ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm,
    fun h g x => (h x).trans (g x)⟩
  add' := by
    intro a b c d hab hcd
    have h₁ := green_add_right hab c
    have h₂ : Green (b+c) (b+d) := by
      simpa only [add_comm] using green_add_right hcd b
    simpa only [add_comm c b, add_comm d b] using
      (show Green (a+c) (b+d) from fun x => (h₁ x).trans (h₂ x))

/-- A sequence sum with the source's empty-sum convention: the empty sequence
sums to an identity only when that identity already exists in the semigroup. -/
def SequenceSum {S : Type*} [AddSemigroup S] : List S → S → Prop
  | [], a => ∀ x : S, a + x = x ∧ x + a = x
  | x :: l, a => l.foldl (· + ·) x = a

/-- Proper subsequences include the empty one. Enumerating unordered sequences
as lists preserves all submultisets and their sums in a commutative semigroup. -/
def IrreducibleAt {S : Type*} [AddSemigroup S] (l : List S) (a : S) : Prop :=
  SequenceSum l a ∧ ∀ u, u.Sublist l → u.length < l.length → ¬ SequenceSum u a

/-- Relative Davenport constant: supremum of irreducible lengths at the given sum. -/
def relativeD {S : Type*} [AddSemigroup S] (a : S) : ℕ∞ :=
  ⨆ (l : List S) (_ : IrreducibleAt l a), (l.length : ℕ∞)

/-- The H-class as a subtype of the actual carrier. -/
def HClass {S : Type*} [Add S] (a : S) := {x : S // Green x a}

/-- Actual translations on H_a realized by an element of S. Equal functions
are identified; no identity is adjoined and the carrier is allowed to be empty. -/
def Gamma {S : Type*} [Add S] (a : S) :=
  {f : HClass a → HClass a // ∃ c : S, ∀ x, (f x).val = c + x.val}

instance gammaAdd {S : Type*} [AddCommSemigroup S] (a : S) : Add (Gamma a) where
  add f g := ⟨f.val ∘ g.val, by
    rcases f.property with ⟨c, hc⟩
    rcases g.property with ⟨d, hd⟩
    exact ⟨c+d, fun x => by simp only [Function.comp_apply, hc, hd, add_assoc]⟩⟩

instance gammaAddCommSemigroup {S : Type*} [AddCommSemigroup S] (a : S) :
    AddCommSemigroup (Gamma a) where
  add_assoc f g h := by apply Subtype.ext; rfl
  add_comm f g := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rcases f.property with ⟨c, hc⟩
    rcases g.property with ⟨d, hd⟩
    change (f.val (g.val x)).val = (g.val (f.val x)).val
    rw [hc, hd, hd, hc]
    ac_rfl

/-- Epsilon detects the whole positive cyclic group property, not just idempotence. -/
def epsilon {S : Type*} [Add S] (a : S) : ℕ∞ := by
  classical
  exact if CyclicIsGroup a then 0 else 1

/-- The exact source right side, with the actual quotient and translation semigroup. -/
def rightSide (S K : Type*) [AddCommSemigroup S] [Field K] : ℕ∞ :=
  ⨆ a : S, epsilon a * relativeD ((greenCon S).toQuotient a) + algebraicD (Gamma a) K

/-- Wang arXiv:2509.18724v1 Conjecture 5.3, over all finite commutative
semigroups and fields, preserving the splitting/characteristic disjunction. -/
def claim : Prop :=
  ∀ (S : Type) [AddCommSemigroup S] [Finite S] (K : Type) [Field K],
    Admissible S K → algebraicD S K = rightSide S K

/-- Six independent basis labels: (b,n), b in {0,1}, n in {0,1,2}. -/
structure Model where
  bit : Fin 2
  level : Fin 3
  deriving DecidableEq, Fintype

/-- Union in the first coordinate and addition truncated at two in the second. -/
def modelAdd (x y : Model) : Model :=
  ⟨max x.bit y.bit, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩

instance modelAddInst : Add Model := ⟨modelAdd⟩
instance modelZero : Zero Model := ⟨⟨0,0⟩⟩

instance modelAddCommMonoid : AddCommMonoid Model where
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul := nsmulRec


private theorem positive_add {S : Type*} [AddSemigroup S] (a : S) (m n : ℕ) :
    positiveMultiple a (m+n+1) = positiveMultiple a m + positiveMultiple a n := by
  induction n with
  | zero => simp [positiveMultiple]
  | succ n ih =>
    calc
      positiveMultiple a (m+(n+1)+1) = positiveMultiple a (m+n+1) + a := by
        rw [show m+(n+1)+1 = (m+n+1)+1 by omega]
        rfl
      _ = positiveMultiple a m + (positiveMultiple a n + a) := by rw [ih, add_assoc]
      _ = positiveMultiple a m + positiveMultiple a (n+1) := rfl

private theorem positive_iter {S : Type*} [AddSemigroup S] (a : S) (m n : ℕ) :
    positiveMultiple (positiveMultiple a m) n = positiveMultiple a (m+(m+1)*n) := by
  induction n with
  | zero => simp [positiveMultiple]
  | succ n ih =>
    rw [positiveMultiple, ih, ← positive_add]
    congr 1
    ring

private theorem positive_idempotent {S : Type*} [AddSemigroup S] (e : S)
    (he : e+e=e) (n : ℕ) : positiveMultiple e n = e := by
  induction n with
  | zero => rfl
  | succ n ih => rw [positiveMultiple, ih, he]

private theorem cyclic_idempotent_unique {S : Type*} [AddSemigroup S] {a e f : S}
    (he : IsCyclicIdempotent a e) (hf : IsCyclicIdempotent a f) : e = f := by
  rcases he with ⟨⟨m, rfl⟩, he⟩
  rcases hf with ⟨⟨n, rfl⟩, hf⟩
  have h₁ := positive_idempotent _ he n
  have h₂ := positive_idempotent _ hf m
  rw [positive_iter] at h₁ h₂
  have hmn : m+(m+1)*n = n+(n+1)*m := by ring
  exact h₁.symm.trans (hmn ▸ h₂)

private theorem cyclic_idempotent_exists {S : Type*} [AddCommSemigroup S] [Finite S]
    (a : S) : ∃ e, IsCyclicIdempotent a e := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  obtain ⟨e, he, hi⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun c : S => continuous_of_discreteTopology) (cyclic a) ⟨a, 0, rfl⟩
    (Set.toFinite (cyclic a)).isCompact (by
      rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
      exact ⟨m+n+1, positive_add a m n⟩)
  exact ⟨e, he, hi⟩

private theorem cyclicIdempotent_spec {S : Type*} [AddCommSemigroup S] [Finite S]
    (a : S) : IsCyclicIdempotent a (cyclicIdempotent a) := by
  classical
  have h := cyclic_idempotent_exists a
  simpa [cyclicIdempotent, dif_pos h] using h.choose_spec

/-- The witness's actual cyclic idempotent label. -/
def modelE (x : Model) : Model := ⟨x.bit, if x.level = 0 then 0 else 2⟩

private theorem model_double : ∀ x : Model, x+x = modelE x := by decide
private theorem model_absorb : ∀ x : Model, modelE x+x = modelE x := by decide
private theorem model_idempotent : ∀ x : Model, modelE x+modelE x = modelE x := by decide

private theorem model_positive (x : Model) (n : ℕ) :
    positiveMultiple x (n+1) = modelE x := by
  induction n with
  | zero => exact model_double x
  | succ n ih => rw [positiveMultiple, ih, model_absorb]

private theorem model_cyclicIdempotent (x : Model) : cyclicIdempotent x = modelE x := by
  apply cyclic_idempotent_unique (cyclicIdempotent_spec x)
  exact ⟨⟨1, model_positive x 0⟩, model_idempotent x⟩

private theorem model_period (x : Model) : period x = 1 := by
  have hm : 1 ∈ {n : ℕ | 0 < n ∧ ∃ k, ∀ m, k ≤ m →
      positiveMultiple x (m+n) = positiveMultiple x m} := by
    refine ⟨by decide, 1, ?_⟩
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp only [model_positive]
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) hm
  · exact le_csInf ⟨1, hm⟩ (fun n hn => hn.1)

private theorem model_exponent : semigroupExponent Model = 1 := by
  unfold semigroupExponent
  apply Nat.dvd_one.mp
  apply Finset.lcm_dvd
  intro x hx
  rw [model_period]

private theorem model_admissible : Admissible Model ℚ := by
  left
  simp [Splitting, model_exponent]

private theorem model_pair_zero (x y : Model) :
    factor x (1 : ℚ) * factor y 1 = 0 := by
  have table : ∀ x y : Model, x = modelE x ∨ y = modelE y ∨
      (x+y = x+modelE y ∧ x+y = modelE x+y ∧ x+y = modelE x+modelE y) := by decide
  rcases table x y with hx | hy | ⟨h₁,h₂,h₃⟩
  · simp [factor, model_cyclicIdempotent, ← hx]
  · simp [factor, model_cyclicIdempotent, ← hy]
  · simp only [factor, model_cyclicIdempotent, sub_mul, mul_sub,
      AddMonoidAlgebra.single_mul_single, mul_one, ← h₁, ← h₂, ← h₃]
    abel

private theorem model_product_zero (l : List Model) (hl : 2 ≤ l.length) :
    factorProduct l (fun _ => (1 : ℚ)) = 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at hl
  · simp at hl
  · cases l with
    | nil => exact model_pair_zero x y
    | cons z l =>
      change factor x 1 * (factor y 1 * factorProduct (z::l) (fun _ => (1:ℚ))) = 0
      rw [← mul_assoc, model_pair_zero, zero_mul]

private theorem model_d_upper : algebraicD Model ℚ ≤ 1 := by
  unfold algebraicD
  refine iSup_le fun l => iSup_le fun hl => ?_
  have hlen : l.length ≤ 1 := by
    by_contra h
    exact hl (fun _ => 1) (fun _ _ => one_ne_zero) (model_product_zero l (by omega))
  exact_mod_cast hlen

/-- The two terms used in the irreducible sequence at a=(1,1). -/
def transient : Model := ⟨0,1⟩
def marker : Model := ⟨1,0⟩
def target : Model := ⟨1,1⟩

private theorem model_d_lower : 1 ≤ algebraicD Model ℚ := by
  have hg : GoodSequence (K := ℚ) [transient] := by
    intro c hc hzero
    have ht := congrArg (fun f : AddMonoidAlgebra ℚ Model => f.coeff transient) hzero
    simpa [factorProduct, factor, model_cyclicIdempotent, transient, modelE] using ht
  exact le_iSup_of_le [transient] (le_iSup_of_le hg (by simp))

private theorem model_d_eq : algebraicD Model ℚ = 1 :=
  le_antisymm model_d_upper model_d_lower

private theorem model_green_eq (a b : Model) : Green a b ↔ a=b := by
  have table : ∀ a b : Model, Green a b ↔ a=b := by
    unfold Green Below
    decide
  exact table a b

private theorem model_quotient_injective :
    Function.Injective (greenCon Model).toQuotient := by
  intro a b h
  exact (model_green_eq a b).mp (Quotient.exact h)

private theorem model_irreducible : IrreducibleAt
    [(greenCon Model).toQuotient transient, (greenCon Model).toQuotient marker]
    ((greenCon Model).toQuotient target) := by
  let q := (greenCon Model).toQuotient
  constructor
  · change q (transient+marker) = q target
    rfl
  · intro u hu hlen hsum
    have hmem := List.mem_sublists.mpr hu
    change u ∈ [[], [q transient], [q marker], [q transient, q marker]] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · have h := (hsum (q 0)).1
      change q (target+0) = q 0 at h
      have he := model_quotient_injective h
      exact (by decide : target+0 ≠ (0 : Model)) he
    · have h := model_quotient_injective hsum
      exact (by decide : transient ≠ target) h
    · have h := model_quotient_injective hsum
      exact (by decide : marker ≠ target) h
    · simp at hlen

private theorem model_epsilon : epsilon target = 1 := by
  classical
  apply if_neg
  rintro ⟨e, ⟨n, rfl⟩, he, _⟩
  have h := he target ⟨0,rfl⟩
  change positiveMultiple target (n+1) = target at h
  rw [model_positive] at h
  exact (by decide : modelE target ≠ target) h

private theorem model_right_lower : 2 ≤ rightSide Model ℚ := by
  have hd : (2 : ℕ∞) ≤ relativeD ((greenCon Model).toQuotient target) :=
    le_iSup_of_le _ (le_iSup_of_le model_irreducible (by simp))
  have hloc : (2 : ℕ∞) ≤ epsilon target *
      relativeD ((greenCon Model).toQuotient target) + algebraicD (Gamma target) ℚ := by
    rw [model_epsilon, one_mul]
    exact hd.trans (le_add_of_nonneg_right zero_le)
  exact hloc.trans (le_iSup (fun a : Model => epsilon a *
    relativeD ((greenCon Model).toQuotient a) + algebraicD (Gamma a) ℚ) target)

/- proof_shape: result: content
   admission_basis: open-problem-resolution (issue #23871)
   Live consumers of the private helpers are the witness bounds and result. -/
/-- The complete published universal equality fails at the admissible rational witness. -/
theorem result : ¬ claim := by
  intro h
  have heq := h Model ℚ model_admissible
  have hbad : (2 : ℕ∞) ≤ 1 := by
    calc
      2 ≤ rightSide Model ℚ := model_right_lower
      _ = algebraicD Model ℚ := heq.symm
      _ = 1 := model_d_eq
  norm_num at hbad

end
end D5.S0.Certificates.Algebra.WangConjecture53Refutation
