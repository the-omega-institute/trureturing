/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFiniteNormalInversion
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite native normal codes invert powers by exact natural rank equations. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge

/-! Finite normal atomic codes retain every mixed pair. Inversion is defined
only by successful predecessor steps, and never by truncated subtraction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedAtomicReplacement (atomic_pair pair_atomic atomic_predecessor)
open NativeImageSaturationInterface

abbrev Code := FreeMagma Nat

private theorem code_of_eq (a b : Nat) :
    (FreeMagma.of a : Code) = FreeMagma.of b ↔ a = b := by
  constructor
  · intro h
    injection h
  · intro h
    cases h
    rfl

private theorem code_pair_eq (A B C D : Code) :
    FreeMagma.mul A B = FreeMagma.mul C D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    injection h with h1 h2
    exact ⟨h1,h2⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def expand : Code → Source
  | .of n => substitution^[n] (.of true)
  | .mul A B => .mul (expand A) (expand B)

def Normal : Code → Prop
  | .of _ => True
  | .mul A B => Normal A ∧ Normal B ∧ ¬ ∃ n, A = .of (n+1) ∧ B = .of n

def smart : Code → Code → Code
  | .of a, .of b => if a = b + 1 then .of (b + 2) else .mul (.of a) (.of b)
  | A, B => .mul A B

def encode : Source → Code
  | .of true => .of 0
  | .of false => .of 1
  | .mul A B => smart (encode A) (encode B)

private theorem smart_expand (A B : Code) :
    expand (smart A B) = .mul (expand A) (expand B) := by
  cases A with
  | of a =>
      cases B with
      | of b =>
          dsimp only [smart]
          split_ifs with eq
          · subst a
            exact NativeRankedEqualityCompiler.atomic_pair b
          · rfl
      | mul C D => rfl
  | mul C D => cases B <;> rfl

private theorem smart_normal {A B : Code} (ha : Normal A) (hb : Normal B) :
    Normal (smart A B) := by
  cases A with
  | of a =>
      cases B with
      | of b =>
          dsimp only [smart]
          split_ifs with eq
          · trivial
          · refine ⟨trivial, trivial, ?_⟩
            rintro ⟨n, h1, h2⟩
            have := (code_of_eq _ _).mp h1
            have := (code_of_eq _ _).mp h2
            omega
      | mul C D => exact ⟨ha, hb, by rintro ⟨n, _, bad⟩; cases bad⟩
  | mul C D =>
      cases B <;> exact ⟨ha, hb, by rintro ⟨n, bad, _⟩; cases bad⟩

private theorem encode_law (g : Source) : Normal (encode g) ∧ expand (encode g) = g := by
  induction g with
  | of b => cases b <;> exact ⟨trivial, rfl⟩
  | mul A B ihA ihB =>
      exact ⟨smart_normal ihA.1 ihB.1,
        (smart_expand _ _).trans (congrArg₂ FreeMagma.mul ihA.2 ihB.2)⟩

/-- A finite predecessor routine. Success means the exact natural equation
q+t=n, including the zero and insufficient-rank boundary cases. -/
def rankInverse : Nat → Nat → Option Nat
  | 0, n => some n
  | _ + 1, 0 => none
  | t + 1, n + 1 => rankInverse t n

private theorem rank_inverse_iff (t n q : Nat) : rankInverse t n = some q ↔ q + t = n := by
  induction t generalizing n with
  | zero => simp only [rankInverse, Nat.add_zero, Option.some.injEq, eq_comm]
  | succ t ih =>
      cases n with
      | zero =>
          change (none : Option Nat) = some q ↔ q + (t + 1) = 0
          constructor
          · intro h; cases h
          · intro h; omega
      | succ n => simpa only [rankInverse, Nat.add_succ, Nat.succ.injEq] using ih n

def shiftCode (t : Nat) : Code → Code
  | .of n => .of (n + t)
  | .mul A B => .mul (shiftCode t A) (shiftCode t B)

def inverseCode (t : Nat) : Code → Option Code
  | .of n => (rankInverse t n).map FreeMagma.of
  | .mul A B => (inverseCode t A).bind fun C =>
      (inverseCode t B).map fun D => .mul C D

private theorem inverse_code_iff (t : Nat) (C D : Code) :
    inverseCode t C = some D ↔ shiftCode t D = C := by
  induction C generalizing D with
  | of n =>
      cases D with
      | of q => simp only [inverseCode, shiftCode, Option.map_eq_some_iff, rank_inverse_iff, code_of_eq, exists_eq_right]
      | mul A B => simp [inverseCode, shiftCode, Option.map_eq_some_iff]
  | mul A B ihA ihB =>
      cases D with
      | of q => simp [inverseCode, shiftCode, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      | mul C D =>
          simp only [inverseCode, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            code_pair_eq, shiftCode]
          constructor
          · rintro ⟨U, hu, V, hv, rfl, rfl⟩
            exact ⟨(ihA U).mp hu, (ihB V).mp hv⟩
          · rintro ⟨ha, hb⟩
            exact ⟨C, (ihA C).mpr ha, D, (ihB D).mpr hb, rfl, rfl⟩

private theorem shift_normal_iff (t : Nat) (C : Code) : Normal (shiftCode t C) ↔ Normal C := by
  induction C with
  | of n => rfl
  | mul A B ihA ihB =>
      simp only [shiftCode, Normal, ihA, ihB]
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      apply not_congr
      cases A with
      | of a =>
          cases B with
          | of b =>
              simp only [shiftCode, code_of_eq]
              constructor
              · rintro ⟨n, h1, h2⟩
                exact ⟨b, by omega, rfl⟩
              · rintro ⟨n, h1, h2⟩
                exact ⟨n + t, by omega, by omega⟩
          | mul C D => simp [shiftCode]
      | mul C D => simp [shiftCode]

private theorem shift_expand (t : Nat) (C : Code) :
    expand (shiftCode t C) = substitution^[t] (expand C) := by
  induction C with
  | of n =>
      change substitution^[n+t] (.of true) = substitution^[t] (substitution^[n] (.of true))
      rw [Nat.add_comm n t, Function.iterate_add_apply]
  | mul A B ihA ihB =>
      change FreeMagma.mul (expand (shiftCode t A)) (expand (shiftCode t B)) = _
      rw [ihA, ihB]
      exact (Function.Semiconj₂.iterate (fun X Y => substitution.map_mul X Y) t _ _).symm

private theorem normal_atomic {C : Code} (normal : Normal C) (n : Nat)
    (eq : embed (expand C) = atomic n) : C = .of n := by
  induction C generalizing n with
  | of q =>
      have image : embed (expand (.of q)) = atomic q := (iterate_embed q (.of true)).symm
      rw [image] at eq
      have ranks := CompletionPositiveDriftRegion.atomic_injective eq
      exact congrArg FreeMagma.of ranks
  | mul A B ihA ihB =>
      obtain ⟨j, rfl, ha, hb⟩ := pair_atomic eq
      exact (normal.2.2 ⟨j, ihA normal.1 _ ha, ihB normal.2.1 _ hb⟩).elim

private theorem normal_image_inverse (t : Nat) (C : Code) (normal : Normal C)
    (image : NativeImage t (embed (expand C))) :
    ∃ D, inverseCode t C = some D := by
  induction C with
  | of n =>
      obtain ⟨X, hx⟩ := image
      have image : embed (expand (.of n)) = atomic n := (iterate_embed n (.of true)).symm
      rw [image] at hx
      obtain ⟨q, hq, _⟩ := atomic_predecessor t n X hx
      exact ⟨.of q, by simp only [inverseCode, (rank_inverse_iff t n q).mpr hq, Option.map_some]⟩
  | mul A B ihA ihB =>
      rcases (native_image_iff t _).mp image with ha | hb | ⟨X, Y, eq, hx, hy⟩
      · have impossible := normal_atomic normal t ha
        cases impossible
      · have impossible := normal_atomic normal (t+1) hb
        cases impossible
      · obtain ⟨eqx, eqy⟩ := node_inj eq
        obtain ⟨C, hc⟩ := ihA normal.1 (eqx.symm ▸ hx)
        obtain ⟨D, hd⟩ := ihB normal.2.1 (eqy.symm ▸ hy)
        exact ⟨.mul C D, by simp only [inverseCode, hc, hd, Option.bind_some, Option.map_some]⟩

/-- Every finite actual image has a computable unique finite normal inverse.
The equation at every primitive rank is q+t=n, with a unique natural q. -/
theorem finite_normal_inverse (t : Nat) (g : Source)
    (image : NativeImage t (embed g)) :
    Normal (encode g) ∧ expand (encode g) = g ∧
    ∃! D : Code, inverseCode t (encode g) = some D ∧ Normal D ∧
      substitution^[t] (expand D) = g := by
  have code := encode_law g
  obtain ⟨D, hd⟩ := normal_image_inverse t (encode g) code.1 (code.2.symm ▸ image)
  have shift := (inverse_code_iff t _ _).mp hd
  refine ⟨code.1, code.2, D, ⟨hd, ?_, ?_⟩, ?_⟩
  · exact (shift_normal_iff t D).mp (shift.symm ▸ code.1)
  · rw [← shift_expand, shift, code.2]
  · intro E he
    exact Option.some.inj (he.1.symm.trans hd)

/-- The exact rank inverse has no phantom solution at n<t and no ambiguity. -/
theorem exact_natural_rank_inverse (t n : Nat) :
    (∀ q, rankInverse t n = some q ↔ q + t = n) ∧
    ((∃ q, rankInverse t n = some q) ↔ t ≤ n) ∧
    (∀ q r, q + t = n → r + t = n → q = r) := by
  refine ⟨rank_inverse_iff t n, ?_, ?_⟩
  · constructor
    · rintro ⟨q, hq⟩
      have := (rank_inverse_iff t n q).mp hq
      omega
    · intro bound
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le bound
      exact ⟨q, (rank_inverse_iff t n q).mpr (by omega)⟩
  · intros
    omega

open PresburgerArithmetic (Affine QF Formula)

abbrev Template := FreeMagma Affine

def templateCode (xs : List Int) : Template → Code
  | .of a => .of (a.eval xs).toNat
  | .mul A B => .mul (templateCode xs A) (templateCode xs B)

def Nonnegative (xs : List Int) : Template → Prop
  | .of a => 0 ≤ a.eval xs
  | .mul A B => Nonnegative xs A ∧ Nonnegative xs B

def equalRank (a b : Affine) : QF :=
  .and (.atom (.le (a.add b.neg))) (.atom (.le (b.add a.neg)))

private theorem equal_rank_correct (a b : Affine) (xs : List Int) :
    (equalRank a b).eval xs = true ↔ a.eval xs = b.eval xs := by
  simp only [equalRank, QF.eval, PresburgerArithmetic.Atom.eval, Bool.and_eq_true,
    decide_eq_true_eq, Affine.eval_add, Affine.eval_neg]
  omega

/-- A finite binary decision tree whose conditions are Presburger formulas. -/
inductive Partition where
  | result : Template → Partition
  | split : QF → Partition → Partition → Partition

def Partition.select (xs : List Int) : Partition → Template
  | .result T => T
  | .split q A B => if q.eval xs then A.select xs else B.select xs

def Partition.bind : Partition → (Template → Partition) → Partition
  | .result T, f => f T
  | .split q A B, f => .split q (A.bind f) (B.bind f)

private theorem select_bind (P : Partition) (f : Template → Partition) (xs : List Int) :
    (P.bind f).select xs = (f (P.select xs)).select xs := by
  induction P with
  | result T => rfl
  | split q A B ihA ihB =>
      simp only [Partition.bind, Partition.select]
      split <;> assumption

/-- Leaf identities remember their complete branch history, including when
two leaves happen to carry equal native expressions. -/
def Partition.Leaf : Partition → Type
  | .result _ => Unit
  | .split _ A B => A.Leaf ⊕ B.Leaf

instance partitionLeafFintype : (P : Partition) → Fintype P.Leaf
  | .result _ => inferInstanceAs (Fintype Unit)
  | .split _ A B =>
      letI := partitionLeafFintype A
      letI := partitionLeafFintype B
      inferInstanceAs (Fintype (A.Leaf ⊕ B.Leaf))

def Partition.output : (P : Partition) → P.Leaf → Template
  | .result T, _ => T
  | .split _ A _, .inl l => A.output l
  | .split _ _ B, .inr l => B.output l

def Partition.guard : (P : Partition) → P.Leaf → QF
  | .result _, _ => .truth
  | .split q A _, .inl l => .and q (A.guard l)
  | .split q _ B, .inr l => .and (.not q) (B.guard l)

private theorem unique_partition_leaf (P : Partition) (xs : List Int) :
    (∃! l : P.Leaf, (P.guard l).eval xs = true) ∧
    ∀ l : P.Leaf, (P.guard l).eval xs = true → P.output l = P.select xs := by
  induction P with
  | result T =>
      exact ⟨⟨(), rfl, fun l _ => by cases l; rfl⟩, fun _ _ => rfl⟩
  | split q A B ihA ihB =>
      obtain ⟨a, ha, ua⟩ := ihA.1
      obtain ⟨b, hb, ub⟩ := ihB.1
      cases hq : q.eval xs with
      | true =>
          refine ⟨⟨.inl a, ?_, ?_⟩, ?_⟩
          · simp only [Partition.guard, QF.eval, hq, ha, Bool.and_self]
          · intro l hl
            cases l with
            | inl l =>
                exact congrArg Sum.inl (ua l (by simpa only [Partition.guard, QF.eval, Bool.and_eq_true] using hl : _ ∧ _).2)
            | inr l => simp [Partition.guard, QF.eval, hq] at hl
          · intro l hl
            cases l with
            | inl l =>
                simpa only [Partition.output, Partition.select, hq, ↓reduceIte] using
                  ihA.2 l (by simpa only [Partition.guard, QF.eval, Bool.and_eq_true] using hl : _ ∧ _).2
            | inr l => simp [Partition.guard, QF.eval, hq] at hl
      | false =>
          refine ⟨⟨.inr b, ?_, ?_⟩, ?_⟩
          · simp only [Partition.guard, QF.eval, hq, hb, Bool.not_false, Bool.true_and]
          · intro l hl
            cases l with
            | inl l => simp [Partition.guard, QF.eval, hq] at hl
            | inr l => exact congrArg Sum.inr (ub l (by simpa only [Partition.guard, QF.eval, Bool.and_eq_true] using hl : _ ∧ _).2)
          · intro l hl
            cases l with
            | inl l => simp [Partition.guard, QF.eval, hq] at hl
            | inr l =>
                simpa only [Partition.output, Partition.select, hq, Bool.false_eq_true, ↓reduceIte] using
                  ihB.2 l (by simpa only [Partition.guard, QF.eval, Bool.and_eq_true] using hl : _ ∧ _).2

def smartPartition : Template → Template → Partition
  | .of a, .of b => .split (equalRank a (b.add (.const 1)))
      (.result (.of (b.add (.const 2)))) (.result (.mul (.of a) (.of b)))
  | A, B => .result (.mul A B)

def normalPartition : Template → Partition
  | .of a => .result (.of a)
  | .mul A B => (normalPartition A).bind fun C =>
      (normalPartition B).bind fun D => smartPartition C D

private theorem smart_partition_correct (A B : Template) (xs : List Int)
    (ha : Nonnegative xs A) (hb : Nonnegative xs B) :
    Nonnegative xs ((smartPartition A B).select xs) ∧
    templateCode xs ((smartPartition A B).select xs) = smart (templateCode xs A) (templateCode xs B) := by
  cases A with
  | of a =>
      cases B with
      | of b =>
          have eq : (equalRank a (b.add (.const 1))).eval xs = true ↔
              (a.eval xs).toNat = (b.eval xs).toNat + 1 := by
            rw [equal_rank_correct, Affine.eval_add, Affine.eval_const]
            dsimp [Nonnegative] at ha hb
            omega
          cases hq : (equalRank a (b.add (.const 1))).eval xs with
          | true =>
              have hn := eq.mp hq
              have bpos : 0 ≤ b.eval xs := hb
              refine ⟨?_, ?_⟩
              · simpa only [smartPartition, Partition.select, hq, ↓reduceIte,
                  Nonnegative, Affine.eval_add, Affine.eval_const] using (by omega : 0 ≤ b.eval xs + 2)
              · simp only [smartPartition, Partition.select, hq, ↓reduceIte,
                  templateCode, smart, hn, Affine.eval_add, Affine.eval_const]
                congr 1
                omega
          | false =>
              have hn : (a.eval xs).toNat ≠ (b.eval xs).toNat + 1 := by
                intro bad
                have := eq.mpr bad
                rw [hq] at this
                cases this
              simp only [smartPartition, Partition.select, hq, Bool.false_eq_true, ↓reduceIte]
              exact ⟨⟨ha,hb⟩, by simp only [templateCode, smart, hn, ite_false]⟩
      | mul C D => exact ⟨⟨ha,hb⟩, rfl⟩
  | mul C D => cases B <;> exact ⟨⟨ha,hb⟩, rfl⟩

private theorem normal_partition_correct (T : Template) (xs : List Int)
    (positive : Nonnegative xs T) :
    Nonnegative xs ((normalPartition T).select xs) ∧
    Normal (templateCode xs ((normalPartition T).select xs)) ∧
    expand (templateCode xs ((normalPartition T).select xs)) = expand (templateCode xs T) := by
  induction T with
  | of a => exact ⟨positive, trivial, rfl⟩
  | mul A B ihA ihB =>
      obtain ⟨pa, na, ea⟩ := ihA positive.1
      obtain ⟨pb, nb, eb⟩ := ihB positive.2
      simp only [normalPartition, select_bind]
      have smartLaw := smart_partition_correct ((normalPartition A).select xs)
        ((normalPartition B).select xs) xs pa pb
      refine ⟨smartLaw.1, ?_, ?_⟩
      · rw [smartLaw.2]
        exact smart_normal na nb
      · rw [smartLaw.2, smart_expand, ea, eb]
        rfl

/-- Subtract in integer affine syntax, with a proved natural-domain equation
for each output index; no natural truncated subtraction occurs. -/
def inverseTemplate (t : Nat) : Template → Template
  | .of a => .of (a.add (.const (-(t : Int))))
  | .mul A B => .mul (inverseTemplate t A) (inverseTemplate t B)

private theorem template_inverse_code (t : Nat) (T : Template) (xs : List Int)
    (positive : Nonnegative xs T) (D : Code)
    (inverse : inverseCode t (templateCode xs T) = some D) :
    Nonnegative xs (inverseTemplate t T) ∧ templateCode xs (inverseTemplate t T) = D := by
  induction T generalizing D with
  | of a =>
      obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp inverse
      have rank := (rank_inverse_iff t (a.eval xs).toNat q).mp hq
      refine ⟨?_, ?_⟩
      · simp only [inverseTemplate, Nonnegative, Affine.eval_add, Affine.eval_const]
        dsimp [Nonnegative] at positive
        omega
      · rw [← eq]
        change FreeMagma.of ((a.add (.const (-(t : Int)))).eval xs).toNat = FreeMagma.of q
        congr 1
        simp only [Affine.eval_add, Affine.eval_const]
        dsimp [Nonnegative] at positive
        omega
  | mul A B ihA ihB =>
      obtain ⟨C, hc, E, he, eq⟩ : ∃ C, inverseCode t (templateCode xs A) = some C ∧
          ∃ E, inverseCode t (templateCode xs B) = some E ∧ FreeMagma.mul C E = D := by
        simpa only [inverseCode, templateCode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] using inverse
      obtain ⟨pa, ea⟩ := ihA positive.1 C hc
      obtain ⟨pb, eb⟩ := ihB positive.2 E he
      exact ⟨⟨pa,pb⟩, (congrArg₂ FreeMagma.mul ea eb).trans eq⟩

/-- A finite, disjoint, exhaustive Presburger partition computes the normal
finite inverse of every symbolic actual image, at the same parameters. -/
theorem symbolic_presburger_inverse (T : Template) (t : Nat) (xs : List Int)
    (positive : Nonnegative xs T) (image : NativeImage t (embed (expand (templateCode xs T)))) :
    (∃! l : (normalPartition T).Leaf, ((normalPartition T).guard l).eval xs = true) ∧
    ∀ l : (normalPartition T).Leaf, ((normalPartition T).guard l).eval xs = true →
      Nonnegative xs (inverseTemplate t ((normalPartition T).output l)) ∧
      Normal (templateCode xs (inverseTemplate t ((normalPartition T).output l))) ∧
      substitution^[t] (expand (templateCode xs (inverseTemplate t ((normalPartition T).output l)))) =
        expand (templateCode xs T) ∧
      ∀ n q, rankInverse t n = some q ↔ q + t = n := by
  have part := unique_partition_leaf (normalPartition T) xs
  refine ⟨part.1, ?_⟩
  intro l hl
  rw [part.2 l hl]
  have normal := normal_partition_correct T xs positive
  obtain ⟨D, hd⟩ := normal_image_inverse t _ normal.2.1 (normal.2.2.symm ▸ image)
  have recovered := template_inverse_code t _ xs normal.1 D hd
  refine ⟨recovered.1, ?_, ?_, fun n q => (exact_natural_rank_inverse t n).1 q⟩
  · rw [recovered.2]
    exact (shift_normal_iff t D).mp (((inverse_code_iff t _ _).mp hd).symm ▸ normal.2.1)
  · rw [recovered.2, ← shift_expand, (inverse_code_iff t _ _).mp hd, normal.2.2]

open NativeGuardedFreeExtension NativeGuardedImageSaturation NativeAffineImageSaturation
open NativeEffectiveImageGuard NativeOriginalReconstructionBridge
open NativeSymbolicFiniteForcing (FiniteExpression finiteValue)

def groundTemplate : Source → Template
  | .of true => .of (.const 0)
  | .of false => .of (.const 1)
  | .mul A B => .mul (groundTemplate A) (groundTemplate B)

private theorem ground_template_law (g : Source) (xs : List Int) :
    Nonnegative xs (groundTemplate g) ∧ expand (templateCode xs (groundTemplate g)) = g := by
  induction g with
  | of b =>
      cases b <;> refine ⟨?_, rfl⟩ <;>
        simp only [groundTemplate, Nonnegative, Affine.eval_const] <;> omega
  | mul A B ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, congrArg₂ FreeMagma.mul ihA.2 ihB.2⟩

/-- The last token is the explicit Omega slot; its numerical rank argument
is zero, and finite symbolic evaluation does not turn Omega into a parameter. -/
def tokenAffine {n k m : Nat} (I : Input n k m) : Fin (k + 1) → Affine :=
  Fin.lastCases (.const 0) I.indices

def finiteTemplate {n k m : Nat} (I : Input n k m) : FiniteExpression (k + 1) → Template
  | .ground g => groundTemplate g
  | .residual c j => .of ((tokenAffine I j).add (.const c))
  | .pair A B => .mul (finiteTemplate I A) (finiteTemplate I B)

private theorem token_affine_law {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (j : Fin (k + 1)) :
    0 ≤ (tokenAffine I j).eval (environment p) ∧
      ((tokenAffine I j).eval (environment p)).toNat = tokenRank (ranks I p) j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [tokenAffine, tokenRank, Fin.lastCases_last, Affine.eval_const]
    exact ⟨le_rfl, rfl⟩
  · simpa only [tokenAffine, tokenRank, Fin.lastCases_castSucc] using
      (show 0 ≤ (I.indices j).eval (environment p) ∧
        ((I.indices j).eval (environment p)).toNat = ranks I p j from ⟨legal.2 j, rfl⟩)

private theorem finite_template_law {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (f : FiniteExpression (k + 1)) :
    Nonnegative (environment p) (finiteTemplate I f) ∧
      expand (templateCode (environment p) (finiteTemplate I f)) =
        finiteValue (tokenRank (ranks I p)) f := by
  induction f with
  | ground g => exact ground_template_law g _
  | residual c j =>
      have rank := token_affine_law I p legal j
      have sum : (((tokenAffine I j).add (.const c)).eval (environment p)).toNat =
          tokenRank (ranks I p) j + c := by
        simp only [Affine.eval_add, Affine.eval_const]
        omega
      refine ⟨?_, ?_⟩
      · change 0 ≤ ((tokenAffine I j).add (.const c)).eval (environment p)
        simp only [Affine.eval_add, Affine.eval_const]
        omega
      · change substitution^[(((tokenAffine I j).add (.const c)).eval (environment p)).toNat]
            (.of true) = substitution^[c] (substitution^[tokenRank (ranks I p) j] (.of true))
        rw [sum, Nat.add_comm, Function.iterate_add_apply]
  | pair A B ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, congrArg₂ FreeMagma.mul ihA.2 ihB.2⟩

/-- A single symbolic finite inverse, with a finite Presburger partition in
the original legal parameter tuple, is shared by all solutions of the mode. -/
theorem original_symbolic_finite_value {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (R : Fin r → Expression k m) (i : Fin r) (f : FiniteExpression (k + 1))
    (finite : finiteImageExpressions I s mode R i = some f)
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)) :
    let P := normalPartition (finiteTemplate I.base f)
    (∃! l : P.Leaf, (P.guard l).eval (environment p) = true) ∧
    ∀ l : P.Leaf, (P.guard l).eval (environment p) = true →
      Nonnegative (environment p) (inverseTemplate (commonShift s) (P.output l)) ∧
      Normal (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l))) ∧
      evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i) =
        embed (expand (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l)))) ∧
      (∀ v, OriginalAdmissible I p v →
        EffectiveInMode (functionalInput I s) mode p (imageValues s v) →
        evaluate (ranks I.base p) v (R i) =
          embed (expand (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l))))) ∧
      (∀ n q, rankInverse (commonShift s) n = some q ↔ q + commonShift s = n) := by
  have original := original_classification_rigidity_prefix I s valid mode R p passing
  have templateLaw := finite_template_law I.base p original.1.1 f
  have forcing := NativeSymbolicFiniteForcing.symbolic_finite_forcing
    (canonicalSystem I s mode) (tokenKind k) (reconstructionImages I s R)
  have fixed := (forcing.2 (tokenRank (ranks I.base p)) i).2 f finite
  have identity := canonical_reconstruction_image I s valid mode p passing R i
  have image : NativeImage (commonShift s)
      (embed (expand (templateCode (environment p) (finiteTemplate I.base f)))) := by
    rw [templateLaw.2, ← fixed.1, identity]
    exact ⟨_,rfl⟩
  have partition := symbolic_presburger_inverse (finiteTemplate I.base f) (commonShift s)
    (environment p) templateLaw.1 image
  refine ⟨partition.1, ?_⟩
  intro l hl
  have inverse := partition.2 l hl
  have canonicalValue : evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i) =
      embed (expand (templateCode (environment p)
        (inverseTemplate (commonShift s) ((normalPartition (finiteTemplate I.base f)).output l)))) := by
    apply (rho_injective.iterate (commonShift s))
    rw [← identity, fixed.1, iterate_embed, inverse.2.2.1, templateLaw.2]
  have finiteMember : i ∈ finiteReconstructions I s mode R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Option.isSome_iff_exists.mpr ⟨f,finite⟩⟩
  obtain ⟨g, hg, rigid⟩ := (original.2 i).2.1 finiteMember
  refine ⟨inverse.1, inverse.2.1, canonicalValue, ?_, inverse.2.2.2⟩
  intro v hv hm
  exact (rigid v hv hm).trans (hg.symm.trans canonicalValue)

#print axioms finite_normal_inverse
#print axioms exact_natural_rank_inverse
#print axioms symbolic_presburger_inverse
#print axioms original_symbolic_finite_value

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion
