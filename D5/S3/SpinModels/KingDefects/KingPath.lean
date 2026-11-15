/- GID: D5/S3/SpinModels/KingDefects/KingPath
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingPath
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Exact orbit counts for paths with a unique monochromatic edge. -/
/-
admission_basis: escape-witness
escape_witness: tail_counts (a uniform decomposition by the next path colour).
errors: proof_shape=bind-only; consumers=tail_counts
tail_split: proof_shape=bind-only; consumers=tail_counts
tail_counts: proof_shape=content; consumers=path_count
The word length and palette are arbitrary. No bounded enumeration, checker,
numerical reduction or certified instance is asserted.
-/
import D5.S3.SpinModels.KingDefects.KingGrid
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Path extension counts and the colour-permutation orbit formula. -/
namespace D5.S3.SpinModels.KingDefects.KingPath
open KingGrid
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private def errors {C : Type*} [DecidableEq C] : {n : ℕ} → C → (Fin n → C) → ℕ
  | 0, _, _ => 0
  | _+1, p, f => (if p = f 0 then 1 else 0) + errors (f 0) (Fin.tail f)

private noncomputable def tail_split {C : Type*} [DecidableEq C]
    (n d : ℕ) (p : C) :
    {f : Fin (n+1) → C // errors p f = d} ≃
      Σ c : C, {f : Fin n → C // (if p=c then 1 else 0)+errors c f=d} where
  toFun f := ⟨f.val 0, Fin.tail f.val, f.property⟩
  invFun q := ⟨Fin.cons q.1 q.2.val, by simpa [errors] using q.2.property⟩
  left_inv f := Subtype.ext (Fin.cons_self_tail _)
  right_inv q := by rcases q with ⟨c,f,h⟩; rfl

private theorem tail_counts {C : Type*} [Fintype C] [DecidableEq C]
    (n : ℕ) (p : C) :
    Nat.card {f : Fin n → C // errors p f = 0} = (Fintype.card C-1)^n ∧
    Nat.card {f : Fin n → C // errors p f = 1} = n*(Fintype.card C-1)^(n-1) := by
  classical
  induction n generalizing p with
  | zero => simp [errors, Nat.card_eq_fintype_card]
  | succ n ih =>
    have hz (c : C) :
        Nat.card {f : Fin n → C // (if p=c then 1 else 0)+errors c f=0} =
          if p=c then 0 else (Fintype.card C-1)^n := by
      by_cases h : p=c
      · simp [h, Nat.card_eq_fintype_card]
      · simpa [h] using (ih c).1
    have ho (c : C) :
        Nat.card {f : Fin n → C // (if p=c then 1 else 0)+errors c f=1} =
          if p=c then (Fintype.card C-1)^n else
            n*(Fintype.card C-1)^(n-1) := by
      by_cases h : p=c
      · simpa [h] using (ih c).1
      · simpa [h] using (ih c).2
    have hpos : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨p⟩
    have hc : (Finset.univ.filter (fun c : C => ¬p=c)).card = Fintype.card C-1 := by
      rw [show Finset.univ.filter (fun c : C => ¬p=c) = Finset.univ.erase p by
        ext c; simp [eq_comm]]
      simp
    constructor
    · rw [Nat.card_congr (tail_split n 0 p), Nat.card_sigma]
      simp_rw [hz]
      simp [Finset.sum_ite, hc, pow_succ, Nat.mul_comm]
    · rw [Nat.card_congr (tail_split n 1 p), Nat.card_sigma]
      simp_rw [ho]
      simp only [Finset.sum_ite, Finset.sum_const, hc, smul_eq_mul]
      have hp : (Finset.univ.filter (fun c : C => p=c)).card = 1 := by simp [eq_comm]
      rw [hp, one_mul]
      cases n with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel, pow_succ]; ring

private def bad {C : Type*} [DecidableEq C] {n : ℕ} (f : Fin n → C) : ℕ :=
  ∑ i : Fin (n-1), if f (lo i) = f (hi i) then 1 else 0

private theorem errors_eq {C : Type*} [DecidableEq C] (n : ℕ)
    (f : Fin (n+1) → C) : bad f = errors (f 0) (Fin.tail f) := by
  induction n with
  | zero => simp [bad, errors]
  | succ n ih =>
    have ht := ih (Fin.tail f)
    simp only [bad, Nat.add_sub_cancel, Fin.sum_univ_succ] at ht ⊢
    simp only [errors, Fin.tail]
    rw [← ht]
    rfl

private theorem errors_map {C D : Type*} [DecidableEq C] [DecidableEq D]
    (e : C → D) (he : Function.Injective e) {n : ℕ} (p : C) (f : Fin n → C) :
    errors (e p) (e ∘ f) = errors p f := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [errors, Function.comp_apply, he.eq_iff]; rw [← ih]; rfl

private theorem bad_map {C D : Type*} [DecidableEq C] [DecidableEq D]
    (e : C → D) (he : Function.Injective e) {n : ℕ} (f : Fin n → C) :
    bad (e ∘ f) = bad f := by simp [bad, he.eq_iff]

private noncomputable def root_split {C : Type*} [DecidableEq C] (n : ℕ) :
    {f : Fin (n+1) → C // bad f=1} ≃
      Σ c : C, {f : Fin n → C // errors c f=1} where
  toFun f := ⟨f.val 0, Fin.tail f.val, (errors_eq n f.val).symm.trans f.property⟩
  invFun q := ⟨Fin.cons q.1 q.2.val, by
    rw [errors_eq]; simpa using q.2.property⟩
  left_inv f := Subtype.ext (Fin.cons_self_tail _)
  right_inv q := by rcases q with ⟨c,f,h⟩; rfl

private theorem path_count {C : Type*} [Fintype C] [DecidableEq C] (n : ℕ) :
    Nat.card {f : Fin (n+1) → C // bad f=1} =
      Fintype.card C * n * (Fintype.card C-1)^(n-1) := by
  classical
  rw [Nat.card_congr (root_split n), Nat.card_sigma]
  simp_rw [(tail_counts n _).2]
  simp [Nat.mul_assoc]

private abbrev Words (n : ℕ) := {f : Fin n → Fin 4 // bad f=1}

private instance word_action (n : ℕ) : MulAction (Equiv.Perm (Fin 4)) (Words n) where
  smul p f := ⟨p ∘ f.val, by rw [bad_map p p.injective]; exact f.property⟩
  one_smul f := Subtype.ext rfl
  mul_smul p q f := Subtype.ext rfl

private noncomputable def canonical_orbits (n : ℕ) :
    {f : Fin n → Fin 4 // bad f=1 ∧ Canonical f} ≃
      MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (Words n) := by
  classical
  apply Equiv.ofBijective (fun f => Quotient.mk _ (⟨f.val,f.property.1⟩ : Words n))
  constructor
  · intro f g h
    obtain ⟨p,hp⟩ := Quotient.exact h
    have he : p ∘ g.val = f.val := congrArg Subtype.val hp
    obtain ⟨u,hu,uniq⟩ := canonical_exists_unique g.val
    have hf := uniq f.val ⟨f.property.2,p,he.symm⟩
    have hg := uniq g.val ⟨g.property.2,Equiv.refl _,rfl⟩
    exact Subtype.ext (hf.trans hg.symm)
  · intro q
    induction q using Quotient.inductionOn with
    | h f =>
      obtain ⟨g,⟨hg,p,hp⟩,_⟩ := canonical_exists_unique f.val
      refine ⟨⟨g,?_,hg⟩,?_⟩
      · rw [hp,bad_map p p.injective]; exact f.property
      · exact Quotient.sound ⟨p,Subtype.ext hp.symm⟩

private noncomputable def fixed_words (n : ℕ) (p : Equiv.Perm (Fin 4)) :
    MulAction.fixedBy (Words n) p ≃
      {f : Fin n → {c : Fin 4 // p c=c} // bad f=1} where
  toFun f := ⟨(fun i => ⟨f.val.val i,congrFun (congrArg Subtype.val f.property) i⟩), by
    simpa [bad, Subtype.ext_iff] using f.val.property⟩
  invFun f := ⟨⟨(fun i => (f.val i).val), by
    simpa [bad, Subtype.ext_iff] using f.property⟩, by
    apply Subtype.ext; funext i; exact (f.val i).property⟩
  left_inv f := rfl
  right_inv f := rfl

private theorem burnside (n : ℕ) :
    24 * Nat.card {f : Fin n → Fin 4 // bad f=1 ∧ Canonical f} =
      ∑ p : Equiv.Perm (Fin 4), Nat.card (MulAction.fixedBy (Words n) p) := by
  classical
  letI : Fintype (Words n) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (Words n)) :=
    Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin 4)) (Words n)
  rw [Nat.card_congr (canonical_orbits n)]
  simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.mul_comm] using h.symm

end D5.S3.SpinModels.KingDefects.KingPath
