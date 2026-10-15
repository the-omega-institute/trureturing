/- GID: D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/UniformDescriptorSupport
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Effective admitted presentations and their consumed finite products feed exact shared-source native halt syntax. -/

import D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
import Mathlib.Data.List.Pi
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Fin

import D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
import D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation

open FirstOrder Language GuardedPhaseExecution
abbrev F (α : Type) := presburger.Formula α

/-- Finite encodings and a supplied effective partial decoder require no default inhabitant. -/
structure EffectiveEncoding (α : Type) where
  encode : α → List Nat
  decode : List Nat → Option α
  roundtrip : ∀ a, decode (encode a) = some a

/-- The original family is a subtype of the full register carrier. Rows are
complete supplied finite encodings, with the supplied literal equality. -/
structure Task (S Y : Type) (letters replies : Nat) where
  registerEncoding : EffectiveEncoding S
  rowEncoding : EffectiveEncoding Y
  original : S → Prop
  permitted : List (Fin letters) → Prop
  permitted_decidable : DecidablePred permitted
  update : S → S
  entryEpoch : Nat
  reply : S → {p : List (Fin letters) // permitted p} → Fin replies
  replies_positive : 0 < replies
  target : {u : S // original u} → Y
  row_eq : DecidableEq Y
  defaultRow : Y

namespace Task
variable {S Y : Type} {letters replies : Nat}
abbrev Source (T : Task S Y letters replies) := {u : S // T.original u}
abbrev Literal (T : Task S Y letters replies) := {p : List (Fin letters) // T.permitted p}

def observation (T : Task S Y letters replies) (u : T.Source) (j : Nat) (p : T.Literal) :
    Fin replies := T.reply ((T.update^[j]) u.val) p

def Reached (T : Task S Y letters replies) (absent : Option (Fin replies))
    (z : S) (p : T.Literal) : Prop :=
  match absent with
  | none => True
  | some a => T.reply z p ≠ a
end Task

/-- Finite chart/type indices encode supplied effective enumerations; the
coordinate tuples themselves and all epochs remain unbounded. -/
structure Presentation {S Y : Type} {letters replies : Nat}
    (T : Task S Y letters replies) (charts types : Nat) where
  sourceDim : Fin charts → Nat
  adm : (η : Fin charts) → F (Fin (sourceDim η))
  theta : (η : Fin charts) → {n : Fin (sourceDim η) → Nat // (adm η).Realize n} → T.Source
  theta_bijective : Function.Bijective
    (fun z : Σ η, {n : Fin (sourceDim η) → Nat // (adm η).Realize n} => theta z.1 z.2)
  same : (η θ : Fin charts) → F (Fin (sourceDim η) ⊕ Fin (sourceDim θ))
  same_exact : ∀ η θ n m (hn : (adm η).Realize n) (hm : (adm θ).Realize m),
    (same η θ).Realize (Sum.elim n m) ↔
      T.target (theta η ⟨n, hn⟩) = T.target (theta θ ⟨m, hm⟩)
  descriptorDim : Fin types → Nat
  valid : (b : Fin types) → F (Fin (descriptorDim b))
  real : (b : Fin types) → (Fin (descriptorDim b) → Nat) → T.Literal → Prop
  chooseLiteral : (b : Fin types) → (t : Fin (descriptorDim b) → Nat) →
    (valid b).Realize t → T.Literal
  choose_mem : ∀ b t h, real b t (chooseLiteral b t h)
  descriptorOf : T.Literal → Σ b, (Fin (descriptorDim b) → Nat)
  coverage : ∀ p, (valid (descriptorOf p).1).Realize (descriptorOf p).2 ∧
    real (descriptorOf p).1 (descriptorOf p).2 p
  replyFormula : (η : Fin charts) → (b : Fin types) → Fin replies →
    F ((Fin (sourceDim η) ⊕ Unit) ⊕ Fin (descriptorDim b))
  reply_exact : ∀ η b n j t (hn : (adm η).Realize n) (ht : (valid b).Realize t)
    p, real b t p → ∀ c,
    (replyFormula η b c).Realize (Sum.elim (Sum.elim n (fun _ => j)) t) ↔
      T.observation (theta η ⟨n, hn⟩) j p = c

/-- Content exists only at reached registers. Its action, persistence and rank
law are the original interpretation, rather than an assumed response monotonicity. -/
structure ReachedTransport {S Y : Type} {letters replies : Nat}
    (T : Task S Y letters replies) (maxRank : Nat) where
  rank : Fin replies → Fin (maxRank + 1)
  rank_strict : StrictMono rank
  absent : Option (Fin replies)
  absent_zero : ∀ a, absent = some a → (rank a).val = 0
  Content : T.Literal → Type
  content : (p : T.Literal) → {z : S // T.Reached absent z p} → Content p
  decode : (p : T.Literal) → Content p → Fin replies
  decode_content : ∀ p z h, T.reply z p = decode p (content p ⟨z, h⟩)
  action : (p : T.Literal) → Nat → Content p → Content p
  action_zero : ∀ p w, action p 0 w = w
  action_add : ∀ p a b w, action p (a+b) w = action p b (action p a w)
  persistent : ∀ (u : T.Source) p j a,
    T.Reached absent ((T.update^[j]) u.val) p →
      T.Reached absent ((T.update^[j+a]) u.val) p
  transport : ∀ (u : T.Source) p j a (h : T.Reached absent ((T.update^[j]) u.val) p),
    content p ⟨(T.update^[j+a]) u.val, persistent u p j a h⟩ =
      action p a (content p ⟨(T.update^[j]) u.val, h⟩)
  rank_transport : ∀ (u : T.Source) p j a (h : T.Reached absent ((T.update^[j]) u.val) p),
    rank (decode p (content p ⟨(T.update^[j]) u.val, h⟩)) ≤
      rank (decode p (action p a (content p ⟨(T.update^[j]) u.val, h⟩)))

/-- UDB.6 follows on the original source while updates remain on the full carrier. -/
theorem rank_monotone {S Y : Type} {letters replies q : Nat}
    {T : Task S Y letters replies} (M : ReachedTransport T q)
    (u : T.Source) (p : T.Literal) : Monotone (fun j => M.rank (T.observation u j p)) := by
  intro j k hjk
  by_cases h : T.Reached M.absent ((T.update^[j]) u.val) p
  · have hk : j + (k-j) = k := by omega
    have current := M.decode_content p ((T.update^[j]) u.val) h
    have future := M.decode_content p ((T.update^[j+(k-j)]) u.val)
      (M.persistent u p j (k-j) h)
    rw [M.transport] at future
    change M.rank (T.reply ((T.update^[j]) u.val) p) ≤ M.rank (T.reply ((T.update^[k]) u.val) p)
    rw [← hk, current, future]
    exact M.rank_transport u p j (k-j) h
  · cases ha : M.absent with
    | none => simp [Task.Reached, ha] at h
    | some a =>
      have reply : T.observation u j p = a := by
        simpa only [Task.Reached, ha, not_not, Task.observation] using h
      change (M.rank (T.observation u j p)).val ≤ (M.rank (T.observation u k p)).val
      rw [reply, M.absent_zero a ha]
      exact Nat.zero_le _

/-- Actual installation data contains only physical literals, complete rows and
finite successors. Vector construction materializes its array eagerly. -/
inductive InstalledEntry {S Y : Type} {letters replies : Nat}
    (T : Task S Y letters replies) (size : Nat)
  | read (literal : T.Literal) (next : Vector (Fin size) replies)
  | update (next : Fin size)
  | halt (row : Y)

structure InstalledTable {S Y : Type} {letters replies : Nat}
    (T : Task S Y letters replies) where
  size : Nat
  positive : 0 < size
  start : Fin size
  entries : Vector (InstalledEntry T size) size

namespace InstalledTable
variable {S Y : Type} {letters replies : Nat} {T : Task S Y letters replies}

def program (table : InstalledTable T) (i : Fin table.size) :
    Instruction (Fin table.size) T.Literal (Fin replies) :=
  match table.entries.get i with
  | .read p k => .read p k.get
  | .update k => .update k
  | .halt _ => .halt

/-- Literal execution and stored complete output rows are checked together. -/
def Successful (table : InstalledTable T) : Prop :=
  ∀ u : T.Source, ∃ h J row,
    table.entries.get h = .halt row ∧ row = T.target u ∧
    Run table.program (T.observation u) table.start T.entryEpoch h J
end InstalledTable

/-- Each read state selects one type before numeric descriptor quantification. -/
inductive TypedEntry (size replies types : Nat)
  | read (kind : Fin types) (next : Vector (Fin size) replies)
  | update (next : Fin size)
  | halt
  deriving DecidableEq

structure Skeleton (size replies types : Nat) where
  start : Fin size
  entries : Vector (TypedEntry size replies types) size
  deriving DecidableEq

/-- A supplied equivalence retains every original state and initial state. Type
selection is required only at actual read entries, so empty types permit read-free tables. -/
def reindexSkeleton {Q A : Type} {s c b : Nat} (sigma : Q ≃ Fin s)
    (start : Q) (prog : Q → Instruction Q A (Fin c))
    (kind : ∀ x p k, prog x = .read p k → Fin b) : Skeleton s c b :=
  ⟨sigma start, Vector.ofFn fun i =>
    match h : prog (sigma.symm i) with
    | .read p k => .read (kind (sigma.symm i) p k h) (Vector.ofFn (sigma ∘ k))
    | .update y => .update (sigma y)
    | .halt => .halt⟩

/-- An explicit list product, with no finite-existence choice. -/
def enumTuple {α : Type} (values : List α) (n : Nat) : List (Fin n → α) :=
  (List.pi (List.finRange n) (fun _ => values)).map (fun f i => f i (by simp))

theorem mem_enumTuple {α : Type} (values : List α) (n : Nat) (f : Fin n → α)
    (h : ∀ i, f i ∈ values) : f ∈ enumTuple values n := by
  apply List.mem_map.mpr
  refine ⟨fun i _ => f i, ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (by intro i hi; exact h i)

private theorem materialize_exact {α : Type} {n : Nat} (v : Vector α n) :
    Vector.ofFn v.get = v := by
  apply Vector.ext
  intro i hi
  simp [Vector.get]

def entryList (s c b : Nat) : List (TypedEntry s c b) :=
  ((List.finRange b).flatMap fun kind =>
    (enumTuple (List.finRange s) c).map fun k => .read kind (Vector.ofFn k)) ++
  (List.finRange s).map TypedEntry.update ++ [.halt]

def skeletonList (s c b : Nat) : List (Skeleton s c b) :=
  (List.finRange s).flatMap fun start =>
    (enumTuple (entryList s c b) s).map fun table => ⟨start, Vector.ofFn table⟩

/-- The sigma size is part of each candidate; zero budget contributes no candidate. -/
def candidates (K c b : Nat) : List (Σ s, Skeleton (s+1) c b) :=
  (List.range K).flatMap fun s => (skeletonList (s+1) c b).map (Sigma.mk s)

private theorem entryList_complete {s c b : Nat} (op : TypedEntry s c b) :
    op ∈ entryList s c b := by
  cases op with
  | read kind k =>
      simp only [entryList, List.mem_append, List.mem_flatMap, List.mem_map]
      left; left
      refine ⟨kind, by simp, k.get, mem_enumTuple _ _ _ (by intro i; simp), ?_⟩
      exact congrArg (TypedEntry.read kind) (materialize_exact k)
  | update k => simp [entryList]
  | halt => simp [entryList]

/-- All initials and entries, including unreachable entries, are present. -/
theorem skeletonList_complete {s c b : Nat} (G : Skeleton s c b) :
    G ∈ skeletonList s c b := by
  simp only [skeletonList, List.mem_flatMap, List.mem_map]
  refine ⟨G.start, by simp, G.entries.get,
    mem_enumTuple _ _ _ (fun i => entryList_complete _), ?_⟩
  cases G
  simp only [materialize_exact]

theorem candidates_complete {s K c b : Nat} (G : Skeleton (s+1) c b) (h : s+1 ≤ K) :
    (⟨s, G⟩ : Σ s, Skeleton (s+1) c b) ∈ candidates K c b := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  exact ⟨s, by simp; omega, G, skeletonList_complete G, rfl⟩

namespace Skeleton
variable {s c b : Nat}

def isRead : TypedEntry s c b → Bool
  | .read _ _ => true
  | _ => false

def isHalt : TypedEntry s c b → Bool
  | .halt => true
  | _ => false

abbrev Read (G : Skeleton s c b) := {i : Fin s // isRead (G.entries.get i) = true}
instance readDecidable (G : Skeleton s c b) : DecidablePred
    (fun i => isRead (G.entries.get i) = true) := fun _ => inferInstance
instance readEnumeration (G : Skeleton s c b) : FinEnum G.Read :=
  FinEnum.Subtype.finEnum _

def readCount (G : Skeleton s c b) := FinEnum.card G.Read

def readAt (G : Skeleton s c b) (a : Fin G.readCount) : G.Read := FinEnum.equiv.symm a

def readKind (G : Skeleton s c b) (a : Fin G.readCount) : Fin b :=
  match h : G.entries.get (G.readAt a).val with
  | .read kind _ => kind
  | .update _ => False.elim (by have := (G.readAt a).property; simp [h, isRead] at this)
  | .halt => False.elim (by have := (G.readAt a).property; simp [h, isRead] at this)

def program (G : Skeleton s c b) (i : Fin s) :
    Instruction (Fin s) (Fin G.readCount) (Fin c) :=
  match h : G.entries.get i with
  | .read _ k => .read (FinEnum.equiv ⟨i, by simp [h, isRead]⟩) k.get
  | .update k => .update k
  | .halt => .halt

def halts (G : Skeleton s c b) : List (Fin s) :=
  (List.finRange s).filter fun i => isHalt (G.entries.get i)

theorem mem_halts (G : Skeleton s c b) (h : Fin s) :
    h ∈ G.halts ↔ G.program h = .halt := by
  simp only [halts, List.mem_filter, List.mem_finRange, true_and]
  unfold program
  split <;> simp_all [isHalt]
end Skeleton

/-- Each block has a fixed numeric interval; zero blocks have no coordinates. -/
def blockTotal {r : Nat} (dims : Fin r → Nat) := (List.ofFn dims).sum

def blockOffset {r : Nat} (dims : Fin r → Nat) (a : Fin r) :=
  ((List.ofFn dims).take a.val).sum

private theorem block_bound {r : Nat} (dims : Fin r → Nat) (a : Fin r) :
    blockOffset dims a + dims a ≤ blockTotal dims := by
  have ht := List.sum_take_succ (List.ofFn dims) a.val (by simpa using a.isLt)
  have hall := List.sum_take_add_sum_drop (List.ofFn dims) (a.val+1)
  have hg : (List.ofFn dims)[a.val]'(by simpa using a.isLt) = dims a := by
    rw [List.getElem_ofFn]
  rw [hg] at ht
  dsimp [blockOffset, blockTotal]
  omega

def blockIndex {r : Nat} (dims : Fin r → Nat) (a : Fin r) (k : Fin (dims a)) :
    Fin (blockTotal dims) :=
  ⟨blockOffset dims a + k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt _)
    (block_bound dims a)⟩

private theorem block_index_equiv {r : Nat} (dims : Fin r → Nat)
    (z : Σ a, Fin (dims a)) :
    (blockIndex dims z.1 z.2).val = (finSigmaFinEquiv z).val := by
  rw [finSigmaFinEquiv_apply]
  dsimp [blockIndex, blockOffset]
  congr 1
  rw [List.sum_take_ofFn]
  apply Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
  · intro i hi; simp
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun x : Fin z.1.val => x.val) he)
  · intro j hj
    exact ⟨Fin.castLE z.1.isLt.le j,
      by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact j.isLt, rfl⟩
  · intro i hi; rfl

/-- The computed prefix-offset injection is the pinned finite sigma equivalence. -/
theorem blockIndex_injective {r : Nat} (dims : Fin r → Nat) :
    Function.Injective (fun z : Σ a, Fin (dims a) => blockIndex dims z.1 z.2) := by
  intro x y h
  apply finSigmaFinEquiv.injective
  apply Fin.ext
  rw [← block_index_equiv dims x, ← block_index_equiv dims y]
  exact congrArg Fin.val h

/-- Certified computed block injection used by the actual formula maps. -/
def descriptorLayout {r : Nat} (dims : Fin r → Nat) :
    (Σ a, Fin (dims a)) ↪ Fin (blockTotal dims) :=
  ⟨fun z => blockIndex dims z.1 z.2, blockIndex_injective dims⟩

end D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation

open FirstOrder Language
open D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation (enumTuple mem_enumTuple)
open FirstOrder.Language.presburger
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
open D5.S3.ObserverMemory.Algorithms.ResponsePhasePartition

namespace D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
abbrev F (α : Type) := presburger.Formula α
abbrev T (α : Type) := presburger.Term α

def closeEx {α : Type} {n : Nat} (φ : F (α ⊕ Fin n)) : F α :=
  (BoundedFormula.relabel id φ).exs

def closeAll {α : Type} {n : Nat} (φ : F (α ⊕ Fin n)) : F α :=
  (BoundedFormula.relabel id φ).alls

@[simp] theorem realize_closeEx {α : Type} {n : Nat} (φ : F (α ⊕ Fin n)) (v : α → Nat) :
    (closeEx φ).Realize v ↔ ∃ w : Fin n → Nat, φ.Realize (Sum.elim v w) := by
  simp only [closeEx, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  have h0 (w : Fin (n + 0) → Nat) : w ∘ Fin.natAdd n = (default : Fin 0 → Nat) := Subsingleton.elim _ _
  simp only [h0, Formula.Realize]
  constructor <;> rintro ⟨w, hw⟩ <;> refine ⟨w, ?_⟩ <;> convert hw using 1

@[simp] theorem realize_closeAll {α : Type} {n : Nat} (φ : F (α ⊕ Fin n)) (v : α → Nat) :
    (closeAll φ).Realize v ↔ ∀ w : Fin n → Nat, φ.Realize (Sum.elim v w) := by
  simp only [closeAll, BoundedFormula.realize_alls,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  have h0 (w : Fin (n + 0) → Nat) : w ∘ Fin.natAdd n = (default : Fin 0 → Nat) := Subsingleton.elim _ _
  simp only [h0, Formula.Realize]
  constructor <;> intro h w <;> specialize h w <;> convert h using 1

def leF {α : Type} (s t : T α) : F α :=
  closeEx ((s.relabel Sum.inl + Term.var (Sum.inr (0 : Fin 1))).equal
    (t.relabel Sum.inl))

@[simp] private theorem realize_leF {α : Type} (s t : T α) (v : α → Nat) :
    (leF s t).Realize v ↔ s.realize v ≤ t.realize v := by
  simp only [leF, realize_closeEx, Formula.realize_equal, realize_add,
    Term.realize_relabel, Term.realize_var, Sum.elim_inr, Sum.elim_comp_inl]
  constructor
  · rintro ⟨w, hw⟩; omega
  · intro h; exact ⟨fun _ => t.realize v - s.realize v, by dsimp only; omega⟩

def allF {α β : Type} (l : List β) (f : β → F α) : F α :=
  (l.map f).foldr (· ⊓ ·) ⊤
def anyF {α β : Type} (l : List β) (f : β → F α) : F α :=
  (l.map f).foldr (· ⊔ ·) ⊥

@[simp] theorem realize_allF {α β : Type} (l : List β) (f : β → F α) (v : α → Nat) :
    (allF l f).Realize v ↔ ∀ b ∈ l, (f b).Realize v := by
  simp [allF, Formula.Realize, BoundedFormula.realize_foldr_inf]
@[simp] theorem realize_anyF {α β : Type} (l : List β) (f : β → F α) (v : α → Nat) :
    (anyF l f).Realize v ↔ ∃ b ∈ l, (f b).Realize v := by
  simp [anyF, Formula.Realize, BoundedFormula.realize_foldr_sup]

abbrev Ctx (K d : Nat) := Fin K ⊕ Fin d

def replyMap {K d r : Nat} {dims : Fin r → Nat}
    (desc : (a : Fin r) → Fin (dims a) → Fin K) (a : Fin r) :
    ((Fin d ⊕ Unit) ⊕ Fin (dims a)) → ((Ctx K d ⊕ Fin 2) ⊕ Fin 1)
  | .inl (.inl i) => .inl (.inl (.inr i))
  | .inl (.inr _) => .inr 0
  | .inr k => .inl (.inl (.inl (desc a k)))

def gamma {K d r c : Nat} (dims : Fin r → Nat)
    (desc : (a : Fin r) → Fin (dims a) → Fin K)
    (reply : (a : Fin r) → Fin c → F ((Fin d ⊕ Unit) ⊕ Fin (dims a)))
    (z : Fin r → Fin c) : F (Ctx K d ⊕ Fin 2) :=
  closeAll ((leF (Term.var (.inl (.inr 0))) (Term.var (.inr 0)) ⊓
    leF (Term.var (.inr 0) + 1) (Term.var (.inl (.inr 1)))).imp
    (allF (List.finRange r) fun a => (reply a (z a)).relabel (replyMap desc a)))
private theorem realize_gamma {K d r c : Nat} (dims : Fin r → Nat)
    (desc : (a : Fin r) → Fin (dims a) → Fin K)
    (reply : (a : Fin r) → Fin c → F ((Fin d ⊕ Unit) ⊕ Fin (dims a)))
    (delta : Fin K → Nat) (n : Fin d → Nat) (obs : Nat → Fin r → Fin c)
    (exactReply : ∀ a z j, (reply a z).Realize
      (Sum.elim (Sum.elim n (fun _ => j)) (fun k => delta (desc a k))) ↔ obs j a = z)
    (z : Fin r → Fin c) (a b : Nat) :
    (gamma dims desc reply z).Realize
      (Sum.elim (Sum.elim delta n) (Fin.cons a (fun _ => b))) ↔ Guard obs z a b := by
  simp only [gamma, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    realize_leF, Term.realize_var, realize_add, realize_one,
    Sum.elim_inl, Sum.elim_inr, Fin.cons_zero, Fin.cons_one, realize_allF,
    List.mem_finRange, forall_true_left, Formula.realize_relabel]
  have per (w : Fin 1 → Nat) (i : Fin r) :
      (reply i (z i)).Realize
        (Sum.elim (Sum.elim (Sum.elim delta n) (Fin.cons a (fun _ => b))) w ∘ replyMap desc i) ↔
        obs (w 0) i = z i := by
    convert exactReply i (z i) (w 0) using 1
    apply Iff.of_eq
    apply congrArg (fun v => (reply i (z i)).Realize v)
    funext x
    rcases x with (i | u) | k <;> rfl
  simp_rw [per]
  constructor
  · intro h j hj hk; funext i; exact h (fun _ => j) ⟨hj, by omega⟩ i
  · intro h w hw i; exact congrFun (h (w 0) hw.1 (by omega)) i


variable {Q A R : Type}

def blocks {l : Nat} (t : Fin (l+2) → Nat) (v : Fin (l+1) → A → R) :=
  List.ofFn (fun i => (t i.succ, v i))
private theorem partition_tuple (obs : Nat → A → R) (l J : Nat)
    (t : Fin (l+2) → Nat) (v : Fin (l+1) → A → R) :
    Partition obs (t 0) (J+1) (blocks t v) ↔
      t (Fin.last (l+1)) = J+1 ∧
      ∀ i : Fin (l+1), t i.castSucc < t i.succ ∧ Guard obs (v i) (t i.castSucc) (t i.succ) := by
  induction l with
  | zero => simp only [blocks, List.ofFn_succ, List.ofFn_zero, Partition, Fin.forall_fin_succ, Fin.forall_fin_zero, Fin.last_zero, ← Fin.succ_last, Fin.castSucc_zero, Fin.succ_zero_eq_one]; tauto
  | succ l ih =>
    simp only [blocks, List.ofFn_succ] at ih
    simp only [blocks, List.ofFn_succ, Partition]
    rw [ih (fun i => t i.succ) (fun i => v i.succ)]
    simp only [Fin.forall_fin_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Fin.castSucc_succ, Fin.succ_last]
    tauto

def control {l : Nat} (x : Q) (mid : Fin l → Q) : Fin (l+1) → Q := Fin.cons x mid
private theorem paths_tuple (prog : Q → Instruction Q A R) (l J : Nat) (x h : Q)
    (t : Fin (l+2) → Nat) (v : Fin (l+1) → A → R) :
    PhasePaths prog x (t 0) h J (blocks t v) ↔
      t (Fin.last (l+1)) = J+1 ∧ ∃ mid : Fin l → Q,
      (∀ i : Fin l, Crossing prog (v i.castSucc) (control x mid i.castSucc) (mid i)
        (t i.succ.castSucc - t i.castSucc.castSucc)) ∧
      FixedPath prog (v (Fin.last l)) (control x mid (Fin.last l)) h
        (J - t (Fin.last l).castSucc) := by
  induction l generalizing x with
  | zero => simp [blocks, List.ofFn_succ, PhasePaths, control]
  | succ l ih =>
    simp only [blocks, List.ofFn_succ] at ih
    simp only [blocks, List.ofFn_succ, PhasePaths]
    simp only [ih (t := fun i => t i.succ) (v := fun i => v i.succ), Fin.succ_last]
    constructor
    · rintro ⟨y, cross, terminal, mid, hc, hp⟩
      refine ⟨terminal, Fin.cons y mid, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa [control] using cross
        · simpa [control, Fin.castSucc_succ] using hc i
      · simpa [control, ← Fin.succ_last] using hp
    · rintro ⟨terminal, mid, hc, hp⟩
      have hm : Fin.cons (mid 0) (fun i => mid i.succ) = mid := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      refine ⟨mid 0, ?_, terminal, (fun i => mid i.succ), ?_, ?_⟩
      · simpa [control] using hc 0
      · intro i; simpa [control, Fin.castSucc_succ, hm] using hc i.succ
      · simpa [control, ← Fin.succ_last, hm] using hp


def Witness {l : Nat} (prog : Q → Instruction Q A R) (obs : Nat → A → R)
    (x h : Q) (N J : Nat) (t : Fin (l+2) → Nat) (v : Fin (l+1) → A → R)
    (mid : Fin l → Q) (d : Fin (l+1) → Nat) : Prop :=
  t 0 = N ∧ t (Fin.last (l+1)) = J+1 ∧
  (∀ i, t i.castSucc < t i.succ ∧ Guard obs (v i) (t i.castSucc) (t i.succ)) ∧
  (∀ i : Fin l, t i.castSucc.castSucc + d i.castSucc = t i.succ.castSucc ∧
    Crossing prog (v i.castSucc) (control x mid i.castSucc) (mid i) (d i.castSucc)) ∧
  t (Fin.last l).castSucc + d (Fin.last l) = J ∧
  FixedPath prog (v (Fin.last l)) (control x mid (Fin.last l)) h (d (Fin.last l))
private theorem witness_native {l : Nat} (prog : Q → Instruction Q A R) (obs : Nat → A → R)
    (x h : Q) (N J : Nat) (t : Fin (l+2) → Nat) (v : Fin (l+1) → A → R) :
    (∃ mid d, Witness prog obs x h N J t v mid d) ↔
    t 0 = N ∧ Partition obs N (J+1) (blocks t v) ∧ PhasePaths prog x N h J (blocks t v) := by
  constructor
  · rintro ⟨mid, d, h0, ht, hg, hc, hd, hp⟩
    refine ⟨h0, ?_, ?_⟩
    · rw [← h0, partition_tuple]; exact ⟨ht, hg⟩
    · rw [← h0, paths_tuple]
      refine ⟨ht, mid, ?_, ?_⟩
      · intro i
        have he := (hc i).1
        have count : d i.castSucc = t i.succ.castSucc - t i.castSucc.castSucc := by omega
        simpa only [← count] using (hc i).2
      · have count : d (Fin.last l) = J - t (Fin.last l).castSucc := by omega
        simpa only [← count] using hp
  · rintro ⟨h0, part, paths⟩
    rw [← h0, partition_tuple] at part
    rw [← h0, paths_tuple] at paths
    obtain ⟨_, mid, hc, hp⟩ := paths
    let d : Fin (l+1) → Nat := fun i =>
      if i.val < l then t i.succ - t i.castSucc else J - t i.castSucc
    have di (i : Fin l) : d i.castSucc = t i.succ.castSucc - t i.castSucc.castSucc := by
      simp [d, i.isLt, Fin.castSucc_succ]
    have dl : d (Fin.last l) = J - t (Fin.last l).castSucc := by simp [d]
    refine ⟨mid, d, h0, part.1, part.2, ?_, ?_, ?_⟩
    · intro i
      refine ⟨?_, by simpa [di] using hc i⟩
      have hs := (part.2 i.castSucc).1
      rw [di]; simp only [Fin.castSucc_succ]; omega
    · rw [dl]
      have hs := (part.2 (Fin.last l)).1
      have he := part.1
      have lastSucc : (Fin.last l).succ = Fin.last (l+1) := Fin.succ_last _
      rw [lastSucc] at hs
      omega
    · simpa only [dl] using hp

abbrev W (l : Nat) := Fin ((l+2)+(l+1))
def tv {l : Nat} (w : W l → Nat) (i : Fin (l+2)) : Nat := w (i.castAdd (l+1))
def dv {l : Nat} (w : W l → Nat) (i : Fin (l+1)) : Nat := w (i.natAdd (l+2))
def tTerm {α : Type} {l : Nat} (i : Fin (l+2)) : T ((α ⊕ Unit) ⊕ W l) :=
  Term.var (.inr (i.castAdd (l+1)))
def dTerm {α : Type} {l : Nat} (i : Fin (l+1)) : T ((α ⊕ Unit) ⊕ W l) :=
  Term.var (.inr (i.natAdd (l+2)))
def jTerm {α : Type} {l : Nat} : T ((α ⊕ Unit) ⊕ W l) := Term.var (.inl (.inr ()))

def guardMap {α : Type} {l : Nat} (i : Fin (l+1)) :
    (α ⊕ Fin 2) → ((α ⊕ Unit) ⊕ W l)
  | .inl a => .inl (.inl a)
  | .inr k => .inr ((⟨i.val + k.val, by omega⟩ : Fin (l+2)).castAdd (l+1))

def countMap {α : Type} {l : Nat} (i : Fin (l+1)) : Unit → ((α ⊕ Unit) ⊕ W l) :=
  fun _ => .inr (i.natAdd (l+2))

def phaseDisjunct {α : Type} [Fintype Q] [DecidableEq Q]
    (Γ : (A → R) → F (α ⊕ Fin 2)) (prog : Q → Instruction Q A R)
    (x h : Q) (N l : Nat) (v : Fin (l+1) → A → R) (mid : Fin l → Q) : F (α ⊕ Unit) :=
  closeEx (
    (tTerm (0 : Fin (l+2))).equal (N : T _) ⊓
    (tTerm (Fin.last (l+1))).equal (jTerm + 1) ⊓
    allF (List.finRange (l+1)) (fun i =>
      leF (tTerm i.castSucc + 1) (tTerm i.succ) ⊓ (Γ (v i)).relabel (guardMap i)) ⊓
    allF (List.finRange l) (fun i =>
      (tTerm i.castSucc.castSucc + dTerm i.castSucc).equal (tTerm i.succ.castSucc) ⊓
      (crossingFormula prog (v i.castSucc) (control x mid i.castSucc) (mid i)).relabel
        (countMap i.castSucc)) ⊓
    (tTerm (Fin.last l).castSucc + dTerm (Fin.last l)).equal jTerm ⊓
    (pathFormula prog (v (Fin.last l)) (control x mid (Fin.last l)) h).relabel
      (countMap (Fin.last l)))
private theorem realize_guardLift {α : Type} {l : Nat} (φ : F (α ⊕ Fin 2))
    (cv : α → Nat) (J : Nat) (w : W l → Nat) (i : Fin (l+1)) :
    (φ.relabel (guardMap i)).Realize (Sum.elim (Sum.elim cv (fun _ => J)) w) ↔
    φ.Realize (Sum.elim cv (Fin.cons (tv w i.castSucc) (fun _ => tv w i.succ))) := by
  rw [Formula.realize_relabel]
  apply Iff.of_eq
  apply congrArg (fun v => φ.Realize v)
  funext z
  rcases z with a | k
  · rfl
  · fin_cases k <;> rfl
private theorem realize_countLift {α : Type} {l : Nat} (φ : F Unit)
    (cv : α → Nat) (J : Nat) (w : W l → Nat) (i : Fin (l+1)) :
    (φ.relabel (countMap i)).Realize (Sum.elim (Sum.elim cv (fun _ => J)) w) ↔
    φ.Realize (fun _ => dv w i) := by
  rw [Formula.realize_relabel]; rfl
private theorem realize_phaseDisjunct {α : Type} [Fintype Q] [DecidableEq Q]
    (Γ : (A → R) → F (α ⊕ Fin 2)) (cv : α → Nat) (obs : Nat → A → R)
    (gExact : ∀ z a b, (Γ z).Realize (Sum.elim cv (Fin.cons a (fun _ => b))) ↔ Guard obs z a b)
    (prog : Q → Instruction Q A R) (x h : Q) (N l J : Nat)
    (v : Fin (l+1) → A → R) (mid : Fin l → Q) :
    (phaseDisjunct Γ prog x h N l v mid).Realize (Sum.elim cv (fun _ => J)) ↔
    ∃ w : W l → Nat, Witness prog obs x h N J (tv w) v mid (dv w) := by
  have cp (z : A → R) (x y : Q) (i : Fin (l+1)) (w : W l → Nat) :=
    (realize_countLift (α := α) (crossingFormula prog z x y) cv J w i).trans
      (fixed_response_formulas_correct prog z x y (dv w i)).2
  have pp (z : A → R) (x y : Q) (i : Fin (l+1)) (w : W l → Nat) :=
    (realize_countLift (α := α) (pathFormula prog z x y) cv J w i).trans
      (fixed_response_formulas_correct prog z x y (dv w i)).1
  have gp (z : A → R) (i : Fin (l+1)) (w : W l → Nat) :=
    (realize_guardLift (Γ z) cv J w i).trans (gExact z (tv w i.castSucc) (tv w i.succ))
  simp only [phaseDisjunct, realize_closeEx, Formula.realize_inf, Formula.realize_equal,
    realize_leF, realize_allF, List.mem_finRange, forall_true_left,
    gp, cp, pp, tTerm, dTerm, jTerm, Term.realize_var, realize_natCast,
    realize_add, realize_one, Sum.elim_inl, Sum.elim_inr, Nat.add_one_le_iff,
    tv, dv, Witness, Nat.cast_id, and_assoc]


def haltEpochFormula {α : Type} {s r c : Nat}
    (Γ : (Fin r → Fin c) → F (α ⊕ Fin 2))
    (prog : Fin s → Instruction (Fin s) (Fin r) (Fin c)) (x h : Fin s) (N q : Nat) :
    F (α ⊕ Unit) :=
  anyF (List.range (q*r+1)) fun l =>
    anyF (enumTuple (enumTuple (List.finRange c) r) (l+1)) fun v =>
      anyF (enumTuple (List.finRange s) l) fun mid => phaseDisjunct Γ prog x h N l v mid
private theorem haltEpoch_correct {α : Type} {s r c q : Nat}
    (Γ : (Fin r → Fin c) → F (α ⊕ Fin 2)) (cv : α → Nat) (obs : Nat → Fin r → Fin c)
    (gExact : ∀ z a b, (Γ z).Realize (Sum.elim cv (Fin.cons a (fun _ => b))) ↔ Guard obs z a b)
    (prog : Fin s → Instruction (Fin s) (Fin r) (Fin c)) (x h : Fin s) (N J : Nat)
    (rank : Fin c → Fin (q+1)) (hinj : Function.Injective rank)
    (hmono : ∀ a, Monotone (fun j => rank (obs j a))) :
    (haltEpochFormula Γ prog x h N q).Realize (Sum.elim cv (fun _ => J)) ↔
    Run prog obs x N h J := by
  simp only [haltEpochFormula, realize_anyF, List.mem_range]
  constructor
  · rintro ⟨l, hl, v, hv, mid, hm, realized⟩
    obtain ⟨w, hw⟩ := (realize_phaseDisjunct Γ cv obs gExact prog x h N l J v mid).mp realized
    obtain ⟨h0, partition, paths⟩ :=
      (witness_native prog obs x h N J (tv w) v).mp ⟨mid, dv w, hw⟩
    exact (guarded_phase_execution partition).mp paths
  · intro path
    have lower := run_epochs path
    obtain ⟨bs, part, chain, count⟩ := finite_response_partition obs rank hinj hmono N J lower
    have cap : potential rank obs J ≤ q*r := by
      calc
        potential rank obs J ≤ ∑ _a : Fin r, q :=
          Finset.sum_le_sum (fun a _ => Nat.le_of_lt_succ (rank (obs J a)).isLt)
        _ = q*r := by simp [Nat.mul_comm]
    cases bs with
    | nil => exact part.elim
    | cons first rest =>
      let l := rest.length
      let t : Fin (l+2) → Nat := Fin.cons N (fun i => ((first::rest).get i).1)
      let v : Fin (l+1) → Fin r → Fin c := fun i => ((first::rest).get i).2
      have reconstruct : blocks t v = first::rest := by
        simp only [blocks, t, v, Fin.cons_succ]
        simp only [Prod.mk.eta]
        exact List.ofFn_get (first::rest)
      obtain ⟨mid, d, witness⟩ :=
        (witness_native prog obs x h N J t v).mpr
          ⟨by simp [t], by simpa only [reconstruct] using part,
            by simpa only [reconstruct] using (guarded_phase_execution part).mpr path⟩
      refine ⟨l, ?_, v, ?_, mid, ?_, ?_⟩
      · simp only [List.length_cons] at count; dsimp [l]; omega
      · apply mem_enumTuple; intro i; apply mem_enumTuple; intro a; simp
      · apply mem_enumTuple; intro i; simp
      · apply (realize_phaseDisjunct Γ cv obs gExact prog x h N l J v mid).mpr
        refine ⟨Fin.append t d, ?_⟩
        have htv : tv (Fin.append t d) = t := by funext i; exact Fin.append_left _ _ _
        have hdv : dv (Fin.append t d) = d := by funext i; exact Fin.append_right _ _ _
        simpa only [htv, hdv] using witness

def eventualHaltFormula {α : Type} (φ : F (α ⊕ Unit)) : F α :=
  closeEx (φ.relabel (Sum.map id (fun _ => (0 : Fin 1))))
private theorem realize_eventualHalt {α : Type} (φ : F (α ⊕ Unit)) (cv : α → Nat) :
    (eventualHaltFormula φ).Realize cv ↔ ∃ J : Nat, φ.Realize (Sum.elim cv (fun _ => J)) := by
  simp only [eventualHaltFormula, realize_closeEx, Formula.realize_relabel]
  have ve (w : Fin 1 → Nat) :
      Sum.elim cv w ∘ Sum.map id (fun _ : Unit => (0 : Fin 1)) = Sum.elim cv (fun _ : Unit => w 0) := by
    funext z; cases z <;> rfl
  simp only [ve]
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w 0, hw⟩
  · rintro ⟨J, hJ⟩; exact ⟨fun _ => J, hJ⟩


open UniformDescriptorPresentation

variable {S Y : Type} {letters c charts types s q : Nat}
variable {Tsk : Task S Y letters c}

/-- The layout is computed once from the type at each read occurrence. -/
def dims (P : Presentation Tsk charts types) (G : Skeleton s c types) :
    Fin G.readCount → Nat := fun a => P.descriptorDim (G.readKind a)

def descriptorTuple (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (a : Fin G.readCount) :
    Fin (dims P G a) → Nat := fun k => delta (descriptorLayout (dims P G) ⟨a, k⟩)

def Valid (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) : Prop :=
  ∀ a, (P.valid (G.readKind a)).Realize (descriptorTuple P G delta a)

/-- Any realization is allowed, including literals different from the supplied
canonical choice and repeated literals at distinct read occurrences. -/
def Realizes (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (literals : Fin G.readCount → Tsk.Literal) : Prop :=
  ∀ a, P.real (G.readKind a) (descriptorTuple P G delta a) (literals a)

def chosenLiterals (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (valid : Valid P G delta)
    (a : Fin G.readCount) : Tsk.Literal :=
  P.chooseLiteral (G.readKind a) (descriptorTuple P G delta a) (valid a)

/-- This is proof interpretation, not an installed table. It stores no row and
is never asserted to be the eager literal installation. -/
def literalProgram (G : Skeleton s c types) (literals : Fin G.readCount → Tsk.Literal) :
    Fin s → Instruction (Fin s) Tsk.Literal (Fin c) :=
  transportProgram (Equiv.refl _) literals G.program

def literalObs (G : Skeleton s c types) (u : Tsk.Source)
    (literals : Fin G.readCount → Tsk.Literal) (j : Nat) (a : Fin G.readCount) : Fin c :=
  Tsk.observation u j (literals a)

/-- The guard keeps the same source coordinates and descriptor embeddings
through every quantified epoch and every phase. -/
def Gamma (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (η : Fin charts) (v : Fin G.readCount → Fin c) :
    F ((Fin (blockTotal (dims P G)) ⊕ Fin (P.sourceDim η)) ⊕ Fin 2) :=
  gamma (dims P G) (fun a k => descriptorLayout (dims P G) ⟨a, k⟩)
    (fun a z => P.replyFormula η (G.readKind a) z) v

/-- J+1 delimits the final guard; the final path ends at J and performs no
post-halt update. All internal crossings use the native final-unit-update formula. -/
def haltAt (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (η : Fin charts) (h : Fin s) :
    F ((Fin (blockTotal (dims P G)) ⊕ Fin (P.sourceDim η)) ⊕ Unit) :=
  haltEpochFormula (Gamma P G η) G.program G.start h Tsk.entryEpoch q

def H (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (η : Fin charts) (h : Fin s) :
    F (Fin (blockTotal (dims P G)) ⊕ Fin (P.sourceDim η)) :=
  eventualHaltFormula (haltAt P M G η h)

/-- Exact native support on one admitted original source and every compatible
literal assignment. No source constructor is applied after transport. -/
theorem native_support {Tsk : Task S Y letters c}
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (η : Fin charts)
    (delta : Fin (blockTotal (dims P G)) → Nat) (n : Fin (P.sourceDim η) → Nat)
    (hadm : (P.adm η).Realize n) (hvalid : Valid P G delta)
    (literals : Fin G.readCount → Tsk.Literal) (hreal : Realizes P G delta literals)
    (h : Fin s) (J : Nat) :
    ((haltAt P M G η h).Realize (Sum.elim (Sum.elim delta n) (fun _ => J)) ↔
      Run (literalProgram G literals) (Tsk.observation (P.theta η ⟨n, hadm⟩))
        G.start Tsk.entryEpoch h J) ∧
    ((H P M G η h).Realize (Sum.elim delta n) ↔
      ∃ J, Run (literalProgram G literals) (Tsk.observation (P.theta η ⟨n, hadm⟩))
        G.start Tsk.entryEpoch h J) := by
  let obs := literalObs G (P.theta η ⟨n, hadm⟩) literals
  have primitive a z j := P.reply_exact η (G.readKind a) n j
    (descriptorTuple P G delta a) hadm (hvalid a) (literals a) (hreal a) z
  have gexact v a b := realize_gamma (dims P G) (fun a k => descriptorLayout (dims P G) ⟨a, k⟩)
    (fun a z => P.replyFormula η (G.readKind a) z) delta n obs primitive v a b
  have mono a : Monotone (fun j => M.rank (obs j a)) :=
    rank_monotone M (P.theta η ⟨n, hadm⟩) (literals a)
  have perEpoch J := haltEpoch_correct (Gamma P G η) (Sum.elim delta n) obs gexact
    G.program G.start h Tsk.entryEpoch J M.rank M.rank_strict.injective mono
  have transport J : Run G.program obs G.start Tsk.entryEpoch h J ↔
      Run (literalProgram G literals) (Tsk.observation (P.theta η ⟨n, hadm⟩))
        G.start Tsk.entryEpoch h J := by
    exact run_transport_iff (Equiv.refl _) literals
      (by intro i; simp [literalProgram, transportProgram]) (by intro j a; rfl)
  have exactEpoch J := (perEpoch J).trans (transport J)
  constructor
  · exact exactEpoch J
  · rw [H, realize_eventualHalt]
    exact exists_congr exactEpoch

#print axioms native_support

end D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
