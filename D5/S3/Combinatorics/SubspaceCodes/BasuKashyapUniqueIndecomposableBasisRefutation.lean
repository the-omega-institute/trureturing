/- GID: D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.claim; result=D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result; claim=D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.claim
   digest: A unique indecomposable basis need not imply intersection closure. -/
/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#13819; Refuted)
  Direct frozen dependencies: none; the proof uses pinned Mathlib.
Private auxiliary declarations (all proof_shape: bind-only):
  LinearCode.opAssociative -> LinearCode.IsBasis, LinearCode.sum_empty, LinearCode.sum_singleton, LinearCode.sum_pair
  LinearCode.opCommutative -> LinearCode.IsBasis, LinearCode.sum_empty, LinearCode.sum_singleton, LinearCode.sum_pair
  LinearCode.sum_empty -> klein_basis, klein_unique_basis
  LinearCode.sum_singleton -> klein_basis, klein_unique_basis
  LinearCode.sum_pair -> klein_basis, klein_unique_basis
  wordEquiv_xor -> xor_assoc, xor_comm, xor_zero, xor_self, xor_cancel
  xor_assoc -> kleinCode.assoc
  xor_comm -> kleinCode.comm
  xor_zero -> kleinCode.leftId, kleinCode.rightId
  xor_self -> kleinCode.inverse, kleinCode.self
  mem_coord -> single_mem_coord
  coord_rank -> realize_rank, realize_distance, blockFin_rank
  coord_inf -> realize_inter
  coord_empty -> realize_zero
  single_mem_coord -> coord_injective
  coord_injective -> realize_injective
  blocks_disjoint -> realize_rank
  blocks_card -> realize_rank, realize_distance, family_intersection_missing, family
  support_inter -> realize_inter
  realize_zero -> realize_distance, realizeFin_zero
  realize_rank -> realize_distance, realizeFin_rank
  realize_inter -> realize_distance, realizeFin_inter
  dS_self -> realize_distance
  dS_bot -> realize_distance
  dS_comm -> realize_distance
  realize_distance -> realizeFin_distance
  support_injective -> realize_injective
  realize_injective -> realizeFin_injective
  xor_cancel -> kleinCode.isometry
  klein_op -> klein_indecomposable, klein_basis, klein_unique_basis
  klein_zero -> klein_basis, klein_unique_basis
  klein_indecomposable -> klein_unique_basis, family
  subsets_pair -> klein_basis, klein_unique_basis
  klein_basis -> klein_unique_basis
  klein_unique_basis -> family
  realizeFin_zero -> familyCode
  realizeFin_rank -> family_intersection_missing, family
  blockFin_rank -> family_intersection_missing, family
  realizeFin_injective -> familyCode
  realizeFin_distance -> familyCode
  realizeFin_inter -> family_notclosed, family
  family_intersection_missing -> family_notclosed, family
  family_notclosed -> family
  family -> result
The family theorem is consumed by result at F = ZMod 2, i = 1, a = 2,
b = 2, and n = 5.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.KleinFour

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
noncomputable section
open Module
namespace D5.S3.Combinatorics.SubspaceCodes.BasuKashyapUniqueIndecomposableBasisRefutation

def dS {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (X Y : Submodule F V) : ℤ :=
  (finrank F X : ℤ) + finrank F Y - 2 * finrank F ↥(X ⊓ Y)

structure LinearCode (F V : Type*) [Field F] [AddCommGroup V] [Module F V] where
  U : Set (Submodule F V)
  botMem : (⊥ : Submodule F V) ∈ U
  op : U → U → U
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  comm : ∀ x y, op x y = op y x
  leftId : ∀ x, op ⟨⊥, botMem⟩ x = x
  rightId : ∀ x, op x ⟨⊥, botMem⟩ = x
  inverse : ∀ x, ∃ y, op x y = ⟨⊥, botMem⟩ ∧ op y x = ⟨⊥, botMem⟩
  self : ∀ x, op x x = ⟨⊥, botMem⟩
  isometry : ∀ x y z, dS (op x y).val (op x z).val = dS y.val z.val

namespace LinearCode
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
def codeZero (L : LinearCode F V) : L.U := ⟨⊥, L.botMem⟩
def Indecomposable (L : LinearCode F V) (x : L.U) : Prop :=
  x.val ≠ ⊥ ∧ ¬ ∃ y z : L.U,
    x = L.op y z ∧ finrank F y.val < finrank F x.val ∧ finrank F z.val < finrank F x.val

private instance opAssociative (L : LinearCode F V) : Std.Associative L.op := ⟨L.assoc⟩
private instance opCommutative (L : LinearCode F V) : Std.Commutative L.op := ⟨L.comm⟩

def IsBasis (L : LinearCode F V) (S : Finset L.U) : Prop :=
  ∀ x : L.U, ∃! T : Finset L.U, T ⊆ S ∧ Finset.fold L.op L.codeZero id T = x

def IsIndecomposableBasis (L : LinearCode F V) (S : Finset L.U) : Prop :=
  L.IsBasis S ∧ ∀ x ∈ S, L.Indecomposable x

@[simp]
private theorem sum_empty (L : LinearCode F V) :
    Finset.fold L.op L.codeZero id ∅ = L.codeZero := Finset.fold_empty
@[simp]
private theorem sum_singleton (L : LinearCode F V) (x : L.U) :
    Finset.fold L.op L.codeZero id {x} = x := by
  rw [Finset.fold_singleton]
  exact L.rightId x
private theorem sum_pair (L : LinearCode F V) (x y : L.U) (hne : x ≠ y) :
    Finset.fold L.op L.codeZero id {x,y} = L.op x y := by
  classical
  rw [Finset.fold_insert (by simpa using hne), Finset.fold_singleton]
  exact congrArg (L.op x) (L.rightId y)
end LinearCode

def claim : Prop :=
  ∀ (F : Type) (_ : Field F) (_ : Fintype F) (n : ℕ)
    (L : LinearCode F (Fin n → F)),
    (∃! S : Finset L.U, L.IsIndecomposableBasis S) ↔ InfClosed L.U

private inductive Word | zero | a | b | c deriving DecidableEq
open Word

private def wordEquiv : Word ≃ ZMod 2 × ZMod 2 where
  toFun
    | zero => (0,0) | a => (1,0) | b => (0,1) | c => (1,1)
  invFun v := if v.1 = 0 then (if v.2 = 0 then zero else b)
    else (if v.2 = 0 then a else c)
  left_inv := by intro w; cases w <;> decide
  right_inv := by decide

private def xor (x y : Word) : Word := wordEquiv.symm (wordEquiv x + wordEquiv y)

private theorem wordEquiv_xor (x y : Word) :
    wordEquiv (xor x y) = wordEquiv x + wordEquiv y :=
  wordEquiv.apply_symm_apply _
private theorem xor_assoc (x y z : Word) : xor (xor x y) z = xor x (xor y z) := by
  apply wordEquiv.injective
  rw [wordEquiv_xor,wordEquiv_xor,wordEquiv_xor,wordEquiv_xor]
  exact add_assoc _ _ _
private theorem xor_comm (x y : Word) : xor x y = xor y x := by
  apply wordEquiv.injective
  rw [wordEquiv_xor,wordEquiv_xor]
  exact add_comm _ _
private theorem xor_zero (x : Word) : xor x zero = x := by
  apply wordEquiv.injective
  rw [wordEquiv_xor]
  exact add_zero _
private theorem xor_self (x : Word) : xor x x = zero := by
  apply wordEquiv.injective
  rw [wordEquiv_xor]
  exact IsAddKleinFour.add_self _

private def coord {F κ : Type*} [Field F] (s : Finset κ) : Submodule F (κ → F) :=
  ⨅ j ∈ (↑s : Set κ)ᶜ, LinearMap.ker (LinearMap.proj j : (κ → F) →ₗ[F] F)
private theorem mem_coord {F κ : Type*} [Field F] (s : Finset κ) (v : κ → F) :
    v ∈ coord (F := F) s ↔ ∀ j ∉ s, v j = 0 := by
  simp [coord, Submodule.mem_iInf, LinearMap.mem_ker]
private theorem coord_rank {F κ : Type*} [Field F] [Fintype κ] (s : Finset κ) :
    finrank F (coord (F := F) s) = s.card := by
  classical
  let e := LinearMap.iInfKerProjEquiv F (fun _ : κ => F)
    (I := (↑s : Set κ)) (J := (↑s : Set κ)ᶜ)
    disjoint_compl_right (by simp)
  change finrank F ↥(⨅ j ∈ (↑s : Set κ)ᶜ,
    LinearMap.ker (LinearMap.proj j : (κ → F) →ₗ[F] F)) = s.card
  rw [e.finrank_eq, Module.finrank_pi]
  exact Fintype.card_coe s
private theorem coord_inf {F κ : Type*} [Field F] [DecidableEq κ] (s t : Finset κ) :
    coord (F := F) s ⊓ coord t = coord (s ∩ t) := by
  unfold coord
  rw [Finset.coe_inter, Set.compl_inter, iInf_union]
private theorem coord_empty {F κ : Type*} [Field F] : coord (F := F) (∅ : Finset κ) = ⊥ := by
  simpa [coord] using (LinearMap.iInf_ker_proj (R := F) (φ := fun _ : κ => F))
private theorem single_mem_coord {F κ : Type*} [Field F] [DecidableEq κ] (s : Finset κ) (j : κ) :
    Pi.single j (1 : F) ∈ coord s ↔ j ∈ s := by
  rw [mem_coord]
  constructor
  · intro h
    by_contra hj
    have hh := h j hj
    simp at hh
  · intro hj k hk
    have hkj : k ≠ j := fun h => hk (h.symm ▸ hj)
    simp [hkj]
private theorem coord_injective {F κ : Type*} [Field F] [DecidableEq κ] :
    Function.Injective (coord (F := F) (κ := κ)) := by
  intro s t h
  apply Finset.ext
  intro j
  rw [← single_mem_coord (F := F), ← single_mem_coord (F := F), h]

private def blockI (i a b : ℕ) : Finset (((Fin i ⊕ Fin a) ⊕ Fin b)) :=
  Finset.univ.image (fun x : Fin i => Sum.inl (Sum.inl x))
private def blockP (i a b : ℕ) : Finset (((Fin i ⊕ Fin a) ⊕ Fin b)) :=
  Finset.univ.image (fun x : Fin a => Sum.inl (Sum.inr x))
private def blockQ (i a b : ℕ) : Finset (((Fin i ⊕ Fin a) ⊕ Fin b)) :=
  Finset.univ.image (Sum.inr : Fin b → ((Fin i ⊕ Fin a) ⊕ Fin b))

private def support (i a b : ℕ) : Word → Finset (((Fin i ⊕ Fin a) ⊕ Fin b))
  | zero => ∅
  | Word.a => blockI i a b ∪ blockP i a b
  | Word.b => blockI i a b ∪ blockQ i a b
  | c => blockP i a b ∪ blockQ i a b
private theorem blocks_disjoint (i a b : ℕ) :
    Disjoint (blockI i a b) (blockP i a b) ∧
    Disjoint (blockI i a b) (blockQ i a b) ∧
    Disjoint (blockP i a b) (blockQ i a b) := by
  simp [blockI, blockP, blockQ, Finset.disjoint_left]
private theorem blocks_card (i a b : ℕ) :
    (blockI i a b).card = i ∧ (blockP i a b).card = a ∧ (blockQ i a b).card = b := by
  have hI : Function.Injective (fun x : Fin i => (Sum.inl (Sum.inl x) : ((Fin i ⊕ Fin a) ⊕ Fin b))) := by
    intro x y h; simpa using h
  have hP : Function.Injective (fun x : Fin a => (Sum.inl (Sum.inr x) : ((Fin i ⊕ Fin a) ⊕ Fin b))) := by
    intro x y h; simpa using h
  simp [blockI, blockP, blockQ, Finset.card_image_of_injective _ hI,
    Finset.card_image_of_injective _ hP, Finset.card_image_of_injective _ Sum.inr_injective]

private theorem support_inter (i a b : ℕ) :
    support i a b Word.a ∩ support i a b Word.b = blockI i a b ∧
    support i a b Word.a ∩ support i a b c = blockP i a b ∧
    support i a b Word.b ∩ support i a b c = blockQ i a b := by
  apply And.intro
  · ext x; rcases x with ((x|x)|x) <;> simp [support,blockI,blockP,blockQ]
  apply And.intro
  · ext x; rcases x with ((x|x)|x) <;> simp [support,blockI,blockP,blockQ]
  · ext x; rcases x with ((x|x)|x) <;> simp [support,blockI,blockP,blockQ]

private def weight (i a b : ℕ) : Word → ℕ
  | zero => 0 | Word.a => i+a | Word.b => i+b | c => a+b

private def realize (F : Type*) [Field F] (i a b : ℕ) (w : Word) :
    Submodule F (((Fin i ⊕ Fin a) ⊕ Fin b) → F) := coord (support i a b w)
private theorem realize_zero (F : Type*) [Field F] (i a b : ℕ) :
    realize F i a b zero = ⊥ := coord_empty
private theorem realize_rank (F : Type*) [Field F] (i a b : ℕ) (w : Word) :
    finrank F (realize F i a b w) = weight i a b w := by
  rw [realize, coord_rank]
  have hd := blocks_disjoint i a b
  have hc := blocks_card i a b
  cases w <;> simp [support,weight,Finset.card_union_of_disjoint,hd.1,hd.2.1,hd.2.2,hc.1,hc.2.1,hc.2.2]
private theorem realize_inter (F : Type*) [Field F] (i a b : ℕ) :
    realize F i a b Word.a ⊓ realize F i a b Word.b = coord (blockI i a b) ∧
    realize F i a b Word.a ⊓ realize F i a b c = coord (blockP i a b) ∧
    realize F i a b Word.b ⊓ realize F i a b c = coord (blockQ i a b) := by
  simp only [realize,coord_inf,(support_inter i a b).1,
    (support_inter i a b).2.1,(support_inter i a b).2.2, and_self]

private theorem dS_self {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (X : Submodule F V) : dS X X = 0 := by
  unfold dS; rw [inf_idem]; omega
private theorem dS_bot {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (X : Submodule F V) : dS ⊥ X = finrank F X := by
  unfold dS; rw [bot_inf_eq, finrank_bot]; omega
private theorem dS_comm {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (X Y : Submodule F V) : dS X Y = dS Y X := by
  unfold dS; rw [inf_comm]; ring
private theorem realize_distance (F : Type*) [Field F] (i a b : ℕ) (x y : Word) :
    dS (realize F i a b x) (realize F i a b y) = weight i a b (xor x y) := by
  have hab : dS (realize F i a b Word.a) (realize F i a b Word.b) = (a+b : ℕ) := by
    unfold dS
    rw [(realize_inter F i a b).1, coord_rank, (blocks_card i a b).1,
      realize_rank, realize_rank]
    simp only [weight, Nat.cast_add]; omega
  have hac : dS (realize F i a b Word.a) (realize F i a b c) = (i+b : ℕ) := by
    unfold dS
    rw [(realize_inter F i a b).2.1, coord_rank, (blocks_card i a b).2.1,
      realize_rank, realize_rank]
    simp only [weight, Nat.cast_add]; omega
  have hbc : dS (realize F i a b Word.b) (realize F i a b c) = (i+a : ℕ) := by
    unfold dS
    rw [(realize_inter F i a b).2.2, coord_rank, (blocks_card i a b).2.2,
      realize_rank, realize_rank]
    simp only [weight, Nat.cast_add]; omega
  have hba := (dS_comm (realize F i a b Word.b) (realize F i a b Word.a)).trans hab
  have hca := (dS_comm (realize F i a b c) (realize F i a b Word.a)).trans hac
  have hcb := (dS_comm (realize F i a b c) (realize F i a b Word.b)).trans hbc
  cases x <;> cases y <;>
    simp only [xor, wordEquiv, realize_zero, dS_self, dS_bot, realize_rank, hab,hac,hbc,hba,hca,hcb,weight]
  all_goals first | rfl | (rw [dS_comm, dS_bot, realize_rank]; rfl)

private theorem support_injective (i a b : ℕ) (hi : 0 < i) (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (support i a b) := by
  intro x y h
  have hI := congrArg (fun s => (Sum.inl (Sum.inl ⟨0,hi⟩) : ((Fin i ⊕ Fin a) ⊕ Fin b)) ∈ s) h
  have hP := congrArg (fun s => (Sum.inl (Sum.inr ⟨0,ha⟩) : ((Fin i ⊕ Fin a) ⊕ Fin b)) ∈ s) h
  have hQ := congrArg (fun s => (Sum.inr ⟨0,hb⟩ : ((Fin i ⊕ Fin a) ⊕ Fin b)) ∈ s) h
  cases x <;> cases y <;> simp [support,blockI,blockP,blockQ] at hI hP hQ ⊢
private theorem realize_injective (F : Type*) [Field F] (i a b : ℕ)
    (hi : 0 < i) (ha : 0 < a) (hb : 0 < b) : Function.Injective (realize F i a b) :=
  (coord_injective (F := F)).comp (support_injective i a b hi ha hb)

private theorem xor_cancel (x y z : Word) : xor (xor x y) (xor x z) = xor y z := by
  apply wordEquiv.injective
  rw [wordEquiv_xor,wordEquiv_xor,wordEquiv_xor,wordEquiv_xor]
  calc
    (wordEquiv x + wordEquiv y) + (wordEquiv x + wordEquiv z) = (wordEquiv x + wordEquiv x) + (wordEquiv y + wordEquiv z) := by abel
    _ = wordEquiv y + wordEquiv z := by rw [IsAddKleinFour.add_self,zero_add]

section GenericKlein
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (r : Word → Submodule F V) (hinj : Function.Injective r)
variable (rz : r zero = ⊥) (i a b : ℕ)
variable (rd : ∀ x y, dS (r x) (r y) = weight i a b (xor x y))

private abbrev kleinCode : LinearCode F V where
  U := Set.range r
  botMem := ⟨zero,rz⟩
  op x y := Equiv.ofInjective r hinj (xor ((Equiv.ofInjective r hinj).symm x) ((Equiv.ofInjective r hinj).symm y))
  assoc x y z := by simp [xor_assoc]
  comm x y := by simp [xor_comm]
  leftId x := by
    have hz : (⟨⊥, ⟨zero,rz⟩⟩ : Set.range r) = Equiv.ofInjective r hinj zero := Subtype.ext rz.symm
    rw [hz]; simp only [Equiv.symm_apply_apply, xor_comm zero, xor_zero, Equiv.apply_symm_apply]
  rightId x := by
    have hz : (⟨⊥, ⟨zero,rz⟩⟩ : Set.range r) = Equiv.ofInjective r hinj zero := Subtype.ext rz.symm
    rw [hz]; simp [xor_zero]
  inverse x := by
    refine ⟨x,?_,?_⟩ <;> simp only [xor_self] <;> exact Subtype.ext rz
  self x := by simp only [xor_self]; exact Subtype.ext rz
  isometry x y z := by
    change dS (r (xor ((Equiv.ofInjective r hinj).symm x) ((Equiv.ofInjective r hinj).symm y)))
      (r (xor ((Equiv.ofInjective r hinj).symm x) ((Equiv.ofInjective r hinj).symm z))) = dS y.val z.val
    rw [rd, xor_cancel]
    have hy : y.val = r ((Equiv.ofInjective r hinj).symm y) :=
      congrArg Subtype.val ((Equiv.ofInjective r hinj).apply_symm_apply y).symm
    have hz : z.val = r ((Equiv.ofInjective r hinj).symm z) :=
      congrArg Subtype.val ((Equiv.ofInjective r hinj).apply_symm_apply z).symm
    rw [hy,hz,rd]

@[simp]
private theorem klein_op (x y : Word) :
    (kleinCode r hinj rz i a b rd).op (Equiv.ofInjective r hinj x) (Equiv.ofInjective r hinj y) =
    Equiv.ofInjective r hinj (xor x y) := by simp [kleinCode]
private theorem klein_zero : (kleinCode r hinj rz i a b rd).codeZero = Equiv.ofInjective r hinj zero :=
  Subtype.ext rz.symm

private theorem klein_indecomposable
    (rr : ∀ w, finrank F (r w) = weight i a b w)
    (ha : i < a) (hb : i < b) (w : Word) :
    (kleinCode r hinj rz i a b rd).Indecomposable (Equiv.ofInjective r hinj w) ↔
      w = Word.a ∨ w = Word.b := by
  have nz (x : Word) (hx : x ≠ zero) : r x ≠ ⊥ := by
    intro h; exact hx (hinj (h.trans rz.symm))
  cases w
  · simp [LinearCode.Indecomposable,rz]
  · constructor
    · intro _; exact Or.inl rfl
    · intro _
      refine ⟨nz Word.a (by decide), ?_⟩
      rintro ⟨y,z,h,hy,hz⟩
      obtain ⟨u,rfl⟩ := (Equiv.ofInjective r hinj).surjective y
      obtain ⟨v,rfl⟩ := (Equiv.ofInjective r hinj).surjective z
      have he : Word.a = xor u v := (Equiv.ofInjective r hinj).injective (h.trans (klein_op r hinj rz i a b rd u v))
      change finrank F (r u) < finrank F (r Word.a) at hy
      change finrank F (r v) < finrank F (r Word.a) at hz
      rw [rr,rr] at hy hz
      cases u <;> cases v <;>
        first | (exfalso; exact (by decide : ¬ _) he) | (dsimp only [weight] at hy hz; omega)
  · constructor
    · intro _; exact Or.inr rfl
    · intro _
      refine ⟨nz Word.b (by decide), ?_⟩
      rintro ⟨y,z,h,hy,hz⟩
      obtain ⟨u,rfl⟩ := (Equiv.ofInjective r hinj).surjective y
      obtain ⟨v,rfl⟩ := (Equiv.ofInjective r hinj).surjective z
      have he : Word.b = xor u v := (Equiv.ofInjective r hinj).injective (h.trans (klein_op r hinj rz i a b rd u v))
      change finrank F (r u) < finrank F (r Word.b) at hy
      change finrank F (r v) < finrank F (r Word.b) at hz
      rw [rr,rr] at hy hz
      cases u <;> cases v <;>
        first | (exfalso; exact (by decide : ¬ _) he) | (dsimp only [weight] at hy hz; omega)
  · constructor
    · rintro ⟨_,h⟩
      exfalso
      apply h
      refine ⟨Equiv.ofInjective r hinj Word.a, Equiv.ofInjective r hinj Word.b, ?_,?_,?_⟩
      · rw [klein_op]; rfl
      · change finrank F (r Word.a) < finrank F (r c)
        rw [rr,rr]; simp only [weight]; omega
      · change finrank F (r Word.b) < finrank F (r c)
        rw [rr,rr]; simp only [weight]; omega
    · simp

private theorem subsets_pair {α : Type*} [DecidableEq α] (x y : α) (T : Finset α) (h : T ⊆ {x,y}) :
    T = ∅ ∨ T = {x} ∨ T = {y} ∨ T = {x,y} := by
  have hs : (↑T : Set α) ⊆ ↑({x,y} : Finset α) := Finset.coe_subset.mpr h
  rw [Finset.coe_pair] at hs
  have hh := Set.subset_pair_iff_eq.mp hs
  rcases hh with h | h | h | h
  · exact Or.inl (Finset.coe_injective (h.trans Finset.coe_empty.symm))
  · exact Or.inr (Or.inl (Finset.coe_injective (h.trans (Finset.coe_singleton x).symm)))
  · exact Or.inr (Or.inr (Or.inl (Finset.coe_injective (h.trans (Finset.coe_singleton y).symm))))
  · exact Or.inr (Or.inr (Or.inr (Finset.coe_injective (h.trans Finset.coe_pair.symm))))

private theorem klein_basis :
    (kleinCode r hinj rz i a b rd).IsBasis {Equiv.ofInjective r hinj Word.a,Equiv.ofInjective r hinj Word.b} := by
  classical
  let L := kleinCode r hinj rz i a b rd
  let : Std.Associative L.op := ⟨L.assoc⟩
  let : Std.Commutative L.op := ⟨L.comm⟩
  let e := Equiv.ofInjective r hinj
  have hab : e Word.a ≠ e Word.b := fun h => Word.noConfusion (e.injective h)
  have hsum0 : Finset.fold L.op L.codeZero id ∅ = e zero := (LinearCode.sum_empty L).trans (klein_zero r hinj rz i a b rd)
  have hsuma : Finset.fold L.op L.codeZero id {e Word.a} = e Word.a := LinearCode.sum_singleton L _
  have hsumb : Finset.fold L.op L.codeZero id {e Word.b} = e Word.b := LinearCode.sum_singleton L _
  have hsumc : Finset.fold L.op L.codeZero id {e Word.a,e Word.b} = e c := by
    rw [LinearCode.sum_pair L _ _ hab]; exact klein_op r hinj rz i a b rd Word.a Word.b
  intro x
  obtain ⟨w,rfl⟩ := e.surjective x
  have uniq (T : Finset L.U) (hT : T ⊆ {e Word.a,e Word.b}) :
      T = ∅ ∨ T = {e Word.a} ∨ T = {e Word.b} ∨ T = {e Word.a,e Word.b} := subsets_pair _ _ T hT
  cases w
  · refine ⟨∅,⟨Finset.empty_subset _,hsum0⟩,?_⟩
    rintro T ⟨hT,he⟩
    rcases uniq T hT with h|h|h|h
    · exact h
    · rw [h,hsuma] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsumb] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsumc] at he
      exact False.elim (Word.noConfusion (e.injective he))
  · refine ⟨{e Word.a},⟨by simp [e],hsuma⟩,?_⟩
    rintro T ⟨hT,he⟩
    rcases uniq T hT with h|h|h|h
    · rw [h,hsum0] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · exact h
    · rw [h,hsumb] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsumc] at he
      exact False.elim (Word.noConfusion (e.injective he))
  · refine ⟨{e Word.b},⟨by simp [e],hsumb⟩,?_⟩
    rintro T ⟨hT,he⟩
    rcases uniq T hT with h|h|h|h
    · rw [h,hsum0] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsuma] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · exact h
    · rw [h,hsumc] at he
      exact False.elim (Word.noConfusion (e.injective he))
  · refine ⟨{e Word.a,e Word.b},⟨Finset.Subset.refl _,hsumc⟩,?_⟩
    rintro T ⟨hT,he⟩
    rcases uniq T hT with h|h|h|h
    · rw [h,hsum0] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsuma] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · rw [h,hsumb] at he
      exact False.elim (Word.noConfusion (e.injective he))
    · exact h


private theorem klein_unique_basis
    (rr : ∀ w, finrank F (r w) = weight i a b w)
    (ha : i < a) (hb : i < b) :
    ∃! S : Finset (kleinCode r hinj rz i a b rd).U,
      (kleinCode r hinj rz i a b rd).IsIndecomposableBasis S := by
  classical
  let L := kleinCode r hinj rz i a b rd
  let : Std.Associative L.op := ⟨L.assoc⟩
  let : Std.Commutative L.op := ⟨L.comm⟩
  let e := Equiv.ofInjective r hinj
  have hic := klein_indecomposable r hinj rz i a b rd rr ha hb
  have hinc : ∀ x : L.U, L.Indecomposable x → x = e Word.a ∨ x = e Word.b := by
    intro x hx
    obtain ⟨w,rfl⟩ := e.surjective x
    rcases (hic w).mp hx with h|h <;> subst w
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hab : e Word.a ≠ e Word.b := fun h => Word.noConfusion (e.injective h)
  have hsum0 : Finset.fold L.op L.codeZero id ∅ = e zero := (LinearCode.sum_empty L).trans (klein_zero r hinj rz i a b rd)
  have hsuma : Finset.fold L.op L.codeZero id {e Word.a} = e Word.a := LinearCode.sum_singleton L _
  have hsumb : Finset.fold L.op L.codeZero id {e Word.b} = e Word.b := LinearCode.sum_singleton L _
  have hsumc : Finset.fold L.op L.codeZero id {e Word.a,e Word.b} = e c :=
    (LinearCode.sum_pair L _ _ hab).trans (klein_op r hinj rz i a b rd Word.a Word.b)
  refine ⟨{e Word.a,e Word.b},⟨klein_basis r hinj rz i a b rd,?_⟩,?_⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h|h <;> subst x
    · exact (hic Word.a).mpr (Or.inl rfl)
    · exact (hic Word.b).mpr (Or.inr rfl)
  · intro S hS
    have hsub : S ⊆ {e Word.a,e Word.b} := by
      intro x hx; simpa only [Finset.mem_insert,Finset.mem_singleton] using hinc x (hS.2 x hx)
    have haS : e Word.a ∈ S := by
      obtain ⟨T,⟨hT,he⟩,_⟩ := hS.1 (e Word.a)
      rcases subsets_pair _ _ T (hT.trans hsub) with h|h|h|h
      · rw [h,hsum0] at he; exact False.elim (Word.noConfusion (e.injective he))
      · exact hT (h.symm ▸ Finset.mem_singleton_self _)
      · rw [h,hsumb] at he; exact False.elim (Word.noConfusion (e.injective he))
      · exact hT (h.symm ▸ Finset.mem_insert_self _ _)
    have hbS : e Word.b ∈ S := by
      obtain ⟨T,⟨hT,he⟩,_⟩ := hS.1 (e Word.b)
      rcases subsets_pair _ _ T (hT.trans hsub) with h|h|h|h
      · rw [h,hsum0] at he; exact False.elim (Word.noConfusion (e.injective he))
      · rw [h,hsuma] at he; exact False.elim (Word.noConfusion (e.injective he))
      · exact hT (h.symm ▸ Finset.mem_singleton_self _)
      · exact hT (h.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact Finset.Subset.antisymm hsub (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro haS hbS)
end GenericKlein

private def realizeFin (F : Type*) [Field F] (i a b : ℕ) (w : Word) :
    Submodule F (Fin (i+a+b) → F) := (realize F i a b w).map (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).toLinearMap

private def blockFin (F : Type*) [Field F] (i a b : ℕ) (s : Finset (((Fin i ⊕ Fin a) ⊕ Fin b))) :
    Submodule F (Fin (i+a+b) → F) := (coord s).map (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).toLinearMap
private theorem realizeFin_zero (F : Type*) [Field F] (i a b : ℕ) : realizeFin F i a b zero = ⊥ := by
  rw [realizeFin,realize_zero,Submodule.map_bot]
private theorem realizeFin_rank (F : Type*) [Field F] (i a b : ℕ) (w : Word) :
    finrank F (realizeFin F i a b w) = weight i a b w := by
  rw [realizeFin,LinearEquiv.finrank_map_eq,realize_rank]
private theorem blockFin_rank (F : Type*) [Field F] (i a b : ℕ) (s : Finset (((Fin i ⊕ Fin a) ⊕ Fin b))) :
    finrank F (blockFin F i a b s) = s.card := by
  rw [blockFin,LinearEquiv.finrank_map_eq,coord_rank]
private theorem realizeFin_injective (F : Type*) [Field F] (i a b : ℕ)
    (hi : 0 < i) (ha : 0 < a) (hb : 0 < b) : Function.Injective (realizeFin F i a b) :=
  (Submodule.map_injective_of_injective (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).injective).comp
    (realize_injective F i a b hi ha hb)
private theorem realizeFin_distance (F : Type*) [Field F] (i a b : ℕ) (x y : Word) :
    dS (realizeFin F i a b x) (realizeFin F i a b y) = weight i a b (xor x y) := by
  unfold dS realizeFin
  rw [← Submodule.map_inf _ (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).injective]
  rw [LinearEquiv.finrank_map_eq,LinearEquiv.finrank_map_eq,LinearEquiv.finrank_map_eq]
  exact realize_distance F i a b x y
private theorem realizeFin_inter (F : Type*) [Field F] (i a b : ℕ) :
    realizeFin F i a b Word.a ⊓ realizeFin F i a b Word.b = blockFin F i a b (blockI i a b) ∧
    realizeFin F i a b Word.a ⊓ realizeFin F i a b c = blockFin F i a b (blockP i a b) ∧
    realizeFin F i a b Word.b ⊓ realizeFin F i a b c = blockFin F i a b (blockQ i a b) := by
  have hi := realize_inter F i a b
  dsimp only [realizeFin,blockFin]
  rw [← Submodule.map_inf _ (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).injective,
    ← Submodule.map_inf _ (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).injective,
    ← Submodule.map_inf _ (LinearEquiv.piCongrLeft F (fun _ => F)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin b))).trans finSumFinEquiv)).injective,
    hi.1,hi.2.1,hi.2.2]
  exact ⟨rfl,rfl,rfl⟩


private abbrev familyCode (F : Type*) [Field F] (i a b : ℕ)
    (hi : 0 < i) (ha : i < a) (hb : i < b) : LinearCode F (Fin (i+a+b) → F) :=
  kleinCode (realizeFin F i a b)
    (realizeFin_injective F i a b hi (hi.trans ha) (hi.trans hb))
    (realizeFin_zero F i a b) i a b (realizeFin_distance F i a b)

private theorem family_intersection_missing (F : Type*) [Field F] (i a b : ℕ)
    (hi : 0 < i) (ha : i < a) (hb : i < b) :
    blockFin F i a b (blockI i a b) ∉ (familyCode F i a b hi ha hb).U := by
  rintro ⟨w,hw⟩
  have hdim := congrArg (fun X : Submodule F (Fin (i+a+b) → F) => finrank F X) hw
  rw [realizeFin_rank,blockFin_rank,(blocks_card i a b).1] at hdim
  cases w <;> dsimp only [weight] at hdim <;> omega

private theorem family_notclosed (F : Type*) [Field F] (i a b : ℕ)
    (hi : 0 < i) (ha : i < a) (hb : i < b) :
    ¬ InfClosed (familyCode F i a b hi ha hb).U := by
  intro h
  have hm := @h (realizeFin F i a b Word.a) ⟨Word.a,rfl⟩
    (realizeFin F i a b Word.b) ⟨Word.b,rfl⟩
  rw [(realizeFin_inter F i a b).1] at hm
  exact family_intersection_missing F i a b hi ha hb hm

private theorem family (F : Type*) [Field F] [Fintype F] (i a b : ℕ)
    (hi : 0 < i) (ha : i < a) (hb : i < b) :
    let L := familyCode F i a b hi ha hb
    let I := blockFin F i a b (blockI i a b)
    let P := blockFin F i a b (blockP i a b)
    let Q := blockFin F i a b (blockQ i a b)
    let A := realizeFin F i a b Word.a
    let B := realizeFin F i a b Word.b
    let C := realizeFin F i a b c
    L.U = {⊥,A,B,C} ∧
    (A ⊓ B = I ∧ A ⊓ C = P ∧ B ⊓ C = Q) ∧
    (finrank F I = i ∧ finrank F A = i+a ∧ finrank F B = i+b ∧ finrank F C = a+b) ∧
    (∀ x : L.U, L.Indecomposable x ↔ x.val = A ∨ x.val = B) ∧
    (∃! S : Finset L.U, L.IsIndecomposableBasis S) ∧
    I ∉ L.U ∧ ¬ InfClosed L.U := by
  classical
  dsimp only
  let r := realizeFin F i a b
  let hinj := realizeFin_injective F i a b hi (hi.trans ha) (hi.trans hb)
  have hic := klein_indecomposable r hinj (realizeFin_zero F i a b) i a b
    (realizeFin_distance F i a b) (realizeFin_rank F i a b) ha hb
  refine ⟨?_,realizeFin_inter F i a b,?_,?_,?_,
    family_intersection_missing F i a b hi ha hb,family_notclosed F i a b hi ha hb⟩
  · ext X
    constructor
    · rintro ⟨w,rfl⟩
      cases w <;> simp [realizeFin_zero]
    · intro hX
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hX
      rcases hX with h|h|h|h
      · exact ⟨zero,(realizeFin_zero F i a b).trans h.symm⟩
      · exact ⟨Word.a,h.symm⟩
      · exact ⟨Word.b,h.symm⟩
      · exact ⟨c,h.symm⟩
  · rw [blockFin_rank,(blocks_card i a b).1,realizeFin_rank,realizeFin_rank,realizeFin_rank]
    exact ⟨rfl,rfl,rfl,rfl⟩
  · intro x
    obtain ⟨w,rfl⟩ := (Equiv.ofInjective r hinj).surjective x
    rw [hic w]
    change (w = Word.a ∨ w = Word.b) ↔ (r w = r Word.a ∨ r w = r Word.b)
    exact or_congr hinj.eq_iff.symm hinj.eq_iff.symm
  · exact klein_unique_basis r hinj (realizeFin_zero F i a b) i a b
      (realizeFin_distance F i a b) (realizeFin_rank F i a b) ha hb

theorem result : ¬ claim := by
  intro hc
  let L := familyCode (ZMod 2) 1 2 2 (by decide) (by decide) (by decide)
  have hf := family (ZMod 2) 1 2 2 (by decide) (by decide) (by decide)
  have hu : ∃! S : Finset L.U, L.IsIndecomposableBasis S := hf.2.2.2.2.1
  have hn : ¬ InfClosed L.U := hf.2.2.2.2.2.2
  exact hn ((hc (ZMod 2) inferInstance inferInstance 5 L).mp hu)

end D5.S3.Combinatorics.SubspaceCodes.BasuKashyapUniqueIndecomposableBasisRefutation
