module
import all Init.Grind.AC

/-! Constructive sequence normalization and certificate checking for associative operations. -/

open Lean.Grind.AC
namespace OmegaChecks.InitPort.Alternatives

private theorem seqEqOfBeq {s t : Seq} (h : s.beq' t) : s = t := by
  induction s generalizing t with
  | var x =>
    cases t with
    | var y => exact congrArg Seq.var (Nat.eq_of_beq_eq_true h)
    | cons => contradiction
  | cons x s ih =>
    cases t with
    | var => contradiction
    | cons y t =>
      have both := Bool.and_eq_true_iff.mp (show (x.beq y && s.beq' t) = true from h)
      cases Nat.eq_of_beq_eq_true both.1
      exact congrArg (Seq.cons x) (ih both.2)

public theorem Lean.Grind.AC.diseq_unsat :
    type_of% @_root_.Lean.Grind.AC.diseq_unsat :=
  fun ctx _ _ cert neq => neq (congrArg (Seq.denote ctx) (seqEqOfBeq cert))

private theorem leftAfter {α : Sort u} {a b c : α} (hh : a = b) : a = c → b = c :=
  fun eq => hh.symm.trans eq

private theorem rightAfter {α : Sort u} {a b c : α} (hh : a = b) : c = a → c = b :=
  fun eq => eq.trans hh

private theorem leftNeAfter {α : Sort u} {a b c : α} (hh : a = b) : a ≠ c → b ≠ c :=
  fun ne eq => ne (hh.trans eq)

private theorem rightNeAfter {α : Sort u} {a b c : α} (hh : a = b) : c ≠ a → c ≠ b :=
  fun ne eq => ne (eq.trans hh.symm)

private theorem certifiedChange {α : Sort u} (ctx : Context α) {s t x y : Seq}
    (cert : s.beq' x && t.beq' y) (eq : x.denote ctx = y.denote ctx) :
    s.denote ctx = t.denote ctx := by
  have both := Bool.and_eq_true_iff.mp cert
  rw [seqEqOfBeq both.1, seqEqOfBeq both.2]
  exact eq

private theorem prefixChange {α : Sort u} (ctx : Context α) (assoc : Std.Associative ctx.op)
    {a b tail s t : Seq} (cert : simp_prefix_cert a b tail s t) (eq : a.denote ctx = b.denote ctx) :
    s.denote ctx = t.denote ctx := by
  apply certifiedChange ctx (x := a.concat_k tail) (y := b.concat_k tail) cert
  simp only [Seq.concat_k_eq_concat, @Seq.denote_concat α ctx assoc]
  rw [eq]
public theorem Lean.Grind.AC.eq_simp_lhs_prefix :
    type_of% @_root_.Lean.Grind.AC.eq_simp_lhs_prefix := by
  intro α ctx assoc a b tail s t result cert eq
  exact leftAfter (prefixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.eq_simp_rhs_prefix :
    type_of% @_root_.Lean.Grind.AC.eq_simp_rhs_prefix := by
  intro α ctx assoc a b tail s t result cert eq
  exact rightAfter (prefixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_lhs_prefix :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_lhs_prefix := by
  intro α ctx assoc a b tail s t result cert eq
  exact leftNeAfter (prefixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_rhs_prefix :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_rhs_prefix := by
  intro α ctx assoc a b tail s t result cert eq
  exact rightNeAfter (prefixChange ctx assoc cert eq)

private theorem suffixChange {α : Sort u} (ctx : Context α) (assoc : Std.Associative ctx.op)
    {a b head s t : Seq} (cert : simp_suffix_cert a b head s t) (eq : a.denote ctx = b.denote ctx) :
    s.denote ctx = t.denote ctx := by
  apply certifiedChange ctx (x := head.concat_k a) (y := head.concat_k b) cert
  simp only [Seq.concat_k_eq_concat, @Seq.denote_concat α ctx assoc]
  rw [eq]
public theorem Lean.Grind.AC.eq_simp_lhs_suffix :
    type_of% @_root_.Lean.Grind.AC.eq_simp_lhs_suffix := by
  intro α ctx assoc a b head s t result cert eq
  exact leftAfter (suffixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.eq_simp_rhs_suffix :
    type_of% @_root_.Lean.Grind.AC.eq_simp_rhs_suffix := by
  intro α ctx assoc a b head s t result cert eq
  exact rightAfter (suffixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_lhs_suffix :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_lhs_suffix := by
  intro α ctx assoc a b head s t result cert eq
  exact leftNeAfter (suffixChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_rhs_suffix :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_rhs_suffix := by
  intro α ctx assoc a b head s t result cert eq
  exact rightNeAfter (suffixChange ctx assoc cert eq)

private theorem middleChange {α : Sort u} (ctx : Context α) (assoc : Std.Associative ctx.op)
    {a b head tail s t : Seq} (cert : simp_middle_cert a b head tail s t) (eq : a.denote ctx = b.denote ctx) :
    s.denote ctx = t.denote ctx := by
  apply certifiedChange ctx (x := head.concat_k (a.concat_k tail)) (y := head.concat_k (b.concat_k tail)) cert
  simp only [Seq.concat_k_eq_concat, @Seq.denote_concat α ctx assoc]
  rw [eq]
public theorem Lean.Grind.AC.eq_simp_lhs_middle :
    type_of% @_root_.Lean.Grind.AC.eq_simp_lhs_middle := by
  intro α ctx assoc a b head tail s t result cert eq
  exact leftAfter (middleChange ctx assoc cert eq)

public theorem Lean.Grind.AC.eq_simp_rhs_middle :
    type_of% @_root_.Lean.Grind.AC.eq_simp_rhs_middle := by
  intro α ctx assoc a b head tail s t result cert eq
  exact rightAfter (middleChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_lhs_middle :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_lhs_middle := by
  intro α ctx assoc a b head tail s t result cert eq
  exact leftNeAfter (middleChange ctx assoc cert eq)

public theorem Lean.Grind.AC.diseq_simp_rhs_middle :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_rhs_middle := by
  intro α ctx assoc a b head tail s t result cert eq
  exact rightNeAfter (middleChange ctx assoc cert eq)

private theorem acChange {α : Sort u} (ctx : Context α) (assoc : Std.Associative ctx.op) (comm : Std.Commutative ctx.op)
    {a b c s t : Seq} (cert : simp_ac_cert c a b s t) (eq : a.denote ctx = b.denote ctx) :
    s.denote ctx = t.denote ctx := by
  apply certifiedChange ctx (x := c.union_k a) (y := c.union_k b) cert
  rw [Seq.union_k_eq_union, Seq.union_k_eq_union, @Seq.denote_union α ctx assoc comm,
      @Seq.denote_union α ctx assoc comm, eq]
public theorem Lean.Grind.AC.simp_ac :
    type_of% @_root_.Lean.Grind.AC.simp_ac := by
  intro α ctx assoc comm c a b s t cert eq
  exact acChange ctx assoc comm cert eq

public theorem Lean.Grind.AC.eq_simp_lhs_ac :
    type_of% @_root_.Lean.Grind.AC.eq_simp_lhs_ac := by
  intro α ctx assoc comm c a b s t result cert eq
  exact leftAfter (acChange ctx assoc comm cert eq)

public theorem Lean.Grind.AC.eq_simp_rhs_ac :
    type_of% @_root_.Lean.Grind.AC.eq_simp_rhs_ac := by
  intro α ctx assoc comm c a b s t result cert eq
  exact rightAfter (acChange ctx assoc comm cert eq)

public theorem Lean.Grind.AC.diseq_simp_lhs_ac :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_lhs_ac := by
  intro α ctx assoc comm c a b s t result cert eq
  exact leftNeAfter (acChange ctx assoc comm cert eq)

public theorem Lean.Grind.AC.diseq_simp_rhs_ac :
    type_of% @_root_.Lean.Grind.AC.diseq_simp_rhs_ac := by
  intro α ctx assoc comm c a b s t result cert eq
  exact rightNeAfter (acChange ctx assoc comm cert eq)

private theorem certifiedDenotation {α : Sort u} (ctx : Context α) {s t : Seq} {value : α}
    (h : s.beq' t) (sound : s.denote ctx = value) : t.denote ctx = value := by
  rw [← seqEqOfBeq h]
  exact sound

private theorem certifiedPair {α : Sort u} (ctx : Context α) {l r s t : Seq} {a b : α}
    (test : l.beq' s && r.beq' t) (left : l.denote ctx = a) (right : r.denote ctx = b) :
    s.denote ctx = a ∧ t.denote ctx = b := by
  have h := Bool.and_eq_true_iff.mp test
  exact ⟨certifiedDenotation ctx h.1 left, certifiedDenotation ctx h.2 right⟩
public theorem Lean.Grind.AC.eq_norm_a :
    type_of% @_root_.Lean.Grind.AC.eq_norm_a := by
  intro α ctx assoc a b s t cert h
  have both := certifiedPair ctx cert
    (@Expr.denote_toSeq α ctx assoc a)
    (@Expr.denote_toSeq α ctx assoc b)
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_norm_a :
    type_of% @_root_.Lean.Grind.AC.diseq_norm_a := by
  intro α ctx assoc a b s t cert h
  have both := certifiedPair ctx cert
    (@Expr.denote_toSeq α ctx assoc a)
    (@Expr.denote_toSeq α ctx assoc b)
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.norm_a :
    type_of% @_root_.Lean.Grind.AC.norm_a := by
  intro α ctx assoc a s cert
  exact (certifiedDenotation ctx cert (@Expr.denote_toSeq α ctx assoc a)).symm

public theorem Lean.Grind.AC.eq_norm_ac :
    type_of% @_root_.Lean.Grind.AC.eq_norm_ac := by
  intro α ctx assoc comm a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_sort α ctx assoc comm a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))
    ((@Seq.denote_sort α ctx assoc comm b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b))
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_norm_ac :
    type_of% @_root_.Lean.Grind.AC.diseq_norm_ac := by
  intro α ctx assoc comm a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_sort α ctx assoc comm a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))
    ((@Seq.denote_sort α ctx assoc comm b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b))
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.norm_ac :
    type_of% @_root_.Lean.Grind.AC.norm_ac := by
  intro α ctx assoc comm a s cert
  exact (certifiedDenotation ctx cert ((@Seq.denote_sort α ctx assoc comm a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))).symm

public theorem Lean.Grind.AC.eq_norm_ai :
    type_of% @_root_.Lean.Grind.AC.eq_norm_ai := by
  intro α ctx assoc ident a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))
    ((@Seq.denote_erase0 α ctx ident b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b))
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_norm_ai :
    type_of% @_root_.Lean.Grind.AC.diseq_norm_ai := by
  intro α ctx assoc ident a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))
    ((@Seq.denote_erase0 α ctx ident b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b))
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.norm_ai :
    type_of% @_root_.Lean.Grind.AC.norm_ai := by
  intro α ctx assoc ident a s cert
  exact (certifiedDenotation ctx cert ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a))).symm

public theorem Lean.Grind.AC.eq_norm_aci :
    type_of% @_root_.Lean.Grind.AC.eq_norm_aci := by
  intro α ctx assoc comm ident a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_sort α ctx assoc comm a.toSeq.erase0).trans ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a)))
    ((@Seq.denote_sort α ctx assoc comm b.toSeq.erase0).trans ((@Seq.denote_erase0 α ctx ident b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b)))
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_norm_aci :
    type_of% @_root_.Lean.Grind.AC.diseq_norm_aci := by
  intro α ctx assoc comm ident a b s t cert h
  have both := certifiedPair ctx cert
    ((@Seq.denote_sort α ctx assoc comm a.toSeq.erase0).trans ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a)))
    ((@Seq.denote_sort α ctx assoc comm b.toSeq.erase0).trans ((@Seq.denote_erase0 α ctx ident b.toSeq).trans (@Expr.denote_toSeq α ctx assoc b)))
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.norm_aci :
    type_of% @_root_.Lean.Grind.AC.norm_aci := by
  intro α ctx assoc comm ident a s cert
  exact (certifiedDenotation ctx cert ((@Seq.denote_sort α ctx assoc comm a.toSeq.erase0).trans ((@Seq.denote_erase0 α ctx ident a.toSeq).trans (@Expr.denote_toSeq α ctx assoc a)))).symm

public theorem Lean.Grind.AC.eq_erase_dup :
    type_of% @_root_.Lean.Grind.AC.eq_erase_dup := by
  intro α ctx assoc idemp a b s t cert h
  have both := certifiedPair ctx cert
    (@Seq.denote_eraseDup α ctx assoc idemp a)
    (@Seq.denote_eraseDup α ctx assoc idemp b)
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_erase_dup :
    type_of% @_root_.Lean.Grind.AC.diseq_erase_dup := by
  intro α ctx assoc idemp a b s t cert h
  have both := certifiedPair ctx cert
    (@Seq.denote_eraseDup α ctx assoc idemp a)
    (@Seq.denote_eraseDup α ctx assoc idemp b)
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.eq_erase_dup_rhs :
    type_of% @_root_.Lean.Grind.AC.eq_erase_dup_rhs := by
  intro α ctx assoc idemp l a s cert h
  exact h.trans (certifiedDenotation ctx cert (@Seq.denote_eraseDup α ctx assoc idemp a)).symm

public theorem Lean.Grind.AC.eq_erase0 :
    type_of% @_root_.Lean.Grind.AC.eq_erase0 := by
  intro α ctx _ ident a b s t cert h
  have both := certifiedPair ctx cert
    (@Seq.denote_erase0 α ctx ident a)
    (@Seq.denote_erase0 α ctx ident b)
  exact both.1.trans (h.trans both.2.symm)

public theorem Lean.Grind.AC.diseq_erase0 :
    type_of% @_root_.Lean.Grind.AC.diseq_erase0 := by
  intro α ctx _ ident a b s t cert h
  have both := certifiedPair ctx cert
    (@Seq.denote_erase0 α ctx ident a)
    (@Seq.denote_erase0 α ctx ident b)
  exact fun e => h (both.1.symm.trans (e.trans both.2))

public theorem Lean.Grind.AC.eq_erase0_rhs :
    type_of% @_root_.Lean.Grind.AC.eq_erase0_rhs := by
  intro α ctx _ ident l a s cert h
  exact h.trans (certifiedDenotation ctx cert (@Seq.denote_erase0 α ctx ident a)).symm

end OmegaChecks.InitPort.Alternatives
