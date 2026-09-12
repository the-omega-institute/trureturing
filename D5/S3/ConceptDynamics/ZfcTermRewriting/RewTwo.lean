/- GID: D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcTermRewriting/RewTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Rew for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcSupport.Function
public import D5.S3.ConceptDynamics.ZfcTermRewriting.RewOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Rew.lean, original lines 321-637.
   Modifications: canonical header, import relocation, capacity scope boundaries,
   and an explicit upstream-inferred language binder for strict auto-implicit mode.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace FirstOrder
namespace Rew
open Semiterm
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)
section cast
variable {n'} (h : n = n')

end cast

section castLE

end castLE

section embSubsts

variable {k} (w : Fin k → Semiterm L ξ n)

@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x := by
  simp [embSubsts]

end embSubsts

section ψ

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp [Rew.q]

@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp [Rew.q]

@[simp] lemma q_fvar (x : ξ₁) : ω.q &x = bShift (ω &x) := by simp [Rew.q]

@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp [comp_app]

@[simp] lemma q_comp_bShift_app (t : Semiterm L ξ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this

@[simp] lemma q_id : (Rew.id : Rew L ξ n ξ n).q = Rew.id := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

lemma q_comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by
  ext x
  · cases x using Fin.cases <;> simp [comp_app]
  · simp [comp_app]

lemma q_bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

lemma q_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

lemma q_rewrite (f : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp


end ψ

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

/-- `LO.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦ &(x + 1)`. -/
def shift : SyntacticRew L n n := map id Nat.succ

/-
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSemiterm L (n + 1)) = #x := by simp [free]

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSemiterm L (n + 1)) = &0 := by simp [free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSemiterm L (n + 1)) = &(x + 1) := by simp [free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSemiterm L n) = #(Fin.castSucc x) := by simp [fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp [fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp [fix]

end fix

@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x
  · exact Fin.elim0 x
  · simp [comp_app]

@[simp] lemma subst_mbar_zero_comp_shift_eq_free :
    (subst (L := L) ![&0]).comp shift = free := by ext x <;> simp [comp_app]

@[simp] lemma subst_comp_bShift_eq_id (v : Fin 1 → Semiterm L ξ 0) :
    (subst (L := L) v).comp bShift = Rew.id := by
  ext x
  · exact Fin.elim0 x
  · simp [comp_app]

@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) : free (bShift t) = shift t := by simp [←comp_app]

@[simp] lemma subst_bShift_app (v : Fin 1 → Semiterm L ξ 0) : subst v (bShift t) = t := by simp [←comp_app]

lemma bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.subst ![] := by
  ext x
  · exact x.elim0
  · simp

section ψ

variable (ω : SyntacticRew L n₁ n₂)

@[simp] lemma q_shift : (shift (L := L) (n := n)).q = shift := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

--@[simp] lemma qpow_fix (k : ℕ) : (fix (L := L) (n := n)).qpow k = fix := by

end ψ

def fixitr (n : ℕ) : (m : ℕ) → SyntacticRew L n (n + m)
  |     0 => Rew.id
  | m + 1 => Rew.fix.comp (fixitr n m)

@[simp] lemma fixitr_zero :
    fixitr (L := L) n 0 = Rew.id := by simp [fixitr]

lemma fixitr_succ (m) :
    fixitr (L := L) n (m + 1) = Rew.fix.comp (fixitr n m) := by
  simp [fixitr]

end Syntactic
end Rew
end FirstOrder
end LO
end
