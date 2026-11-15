/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingPath
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Exact orbit counts for paths with a unique monochromatic edge. -/
/-
admission_basis: escape-witness
escape_witness: tail_counts (a uniform decomposition by the next path colour).
errors: proof_shape=bind-only; consumers=errors_eq,root_split,tail_counts,tail_split
tail_split: proof_shape=bind-only; consumers=tail_counts
tail_counts: proof_shape=content; consumers=path_count
bad: proof_shape=bind-only; consumers=Words,bad_map,burnside,canonical_orbits,errors_eq,fixed_words,literal_count,literal_words,oneDefect_path,one_vertex,path_count,root_split,two_vertices
errors_eq: proof_shape=content; consumers=root_split
bad_map: proof_shape=bind-only; consumers=canonical_orbits,word_action
root_split: proof_shape=bind-only; consumers=path_count
path_count: proof_shape=content; consumers=width_one_large
Words: proof_shape=bind-only; consumers=burnside,canonical_orbits,fixed_words,width_one_large,word_action
word_action: proof_shape=bind-only; consumers=none
canonical_orbits: proof_shape=content; consumers=burnside
fixed_words: proof_shape=bind-only; consumers=width_one_large
burnside: proof_shape=bind-only; consumers=width_one_large
fixedCard: proof_shape=bind-only; consumers=permutation_sum,width_one_large
permutation_sum: proof_shape=bind-only; consumers=width_one_large
edge_path: proof_shape=bind-only; consumers=oneDefect_path
oneDefect_path: proof_shape=bind-only; consumers=literal_words
normal_path: proof_shape=bind-only; consumers=literal_words
literal_words: proof_shape=bind-only; consumers=literal_count
literal_count: proof_shape=bind-only; consumers=one_vertex,two_vertices,width_one_large
width_one_large: proof_shape=content; consumers=width_one
one_vertex: proof_shape=bind-only; consumers=width_one
two_vertices: proof_shape=bind-only; consumers=width_one
width_one: proof_shape=content; consumers=HardinA229578.result
The word length and palette are arbitrary. Finite palette identities and boundary
values support this uniform family; no bounded colouring enumeration, checker,
numerical reduction or independent certified instance is asserted.
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Path extension counts and the colour-permutation orbit formula. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingPath
open KingGrid
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private def errors {C : Type*} [DecidableEq C] : {n : ℕ} → C → (Fin n → C) → ℕ
  | 0, _, _ => 0
  | _+1, p, f => (if p = f 0 then 1 else 0) + errors (f 0) (Fin.tail f)

private noncomputable def tail_split {C : Type*} [DecidableEq C]
    (n d : ℕ) (p : C) :
    {f : Fin (n + 1) → C // errors p f = d} ≃
      Σ c : C, {f : Fin n → C // (if p=c then 1 else 0)+errors c f=d} :=
  ((Fin.consEquiv (fun _ : Fin (n+1) => C)).symm.subtypeEquiv
    (by intro f; rfl)).trans
      (Equiv.subtypeProdEquivSigmaSubtype
        (fun c (f : Fin n → C) => (if p=c then 1 else 0) + errors c f = d))

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
      have hp : (Finset.univ.filter (fun c : C => p=c)).card = 1 := by
        rw [show Finset.univ.filter (fun c : C => p=c) = {p} by ext c; simp [eq_comm]]
        simp
      rw [hp, one_mul]
      cases n with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel, pow_succ]; ring

private def bad {C : Type*} [DecidableEq C] {n : ℕ} (f : Fin n → C) : ℕ :=
  ∑ i : Fin (n-1), if f (lo i) = f (hi i) then 1 else 0

private theorem errors_eq {C : Type*} [DecidableEq C] (n : ℕ)
    (f : Fin (n + 1) → C) : bad f = errors (f 0) (Fin.tail f) := by
  induction n with
  | zero => simp [bad, errors]
  | succ n ih =>
    change (∑ i : Fin (n+1), if f i.castSucc = f i.succ then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if f 0=f (Fin.succ 0) then 1 else 0) + bad (Fin.tail f) = _
    rw [ih]
    rfl

private theorem bad_map {C D : Type*} [DecidableEq C] [DecidableEq D]
    (e : C → D) (he : Function.Injective e) {n : ℕ} (f : Fin n → C) :
    bad (e ∘ f) = bad f := by simp [bad, he.eq_iff]

private noncomputable def root_split {C : Type*} [DecidableEq C] (n : ℕ) :
    {f : Fin (n + 1) → C // bad f=1} ≃
      Σ c : C, {f : Fin n → C // errors c f=1} :=
  ((Fin.consEquiv (fun _ : Fin (n+1) => C)).symm.subtypeEquiv
    (by intro f; change bad f=1 ↔ errors (f 0) (Fin.tail f)=1; rw [errors_eq])).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun c (f : Fin n → C) => errors c f=1))

private theorem path_count {C : Type*} [Fintype C] [DecidableEq C] (n : ℕ) :
    Nat.card {f : Fin (n + 1) → C // bad f=1} =
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
  let : Fintype (Words n) := Fintype.ofFinite _
  let : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (Words n)) :=
    Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin 4)) (Words n)
  rw [Nat.card_congr (canonical_orbits n)]
  norm_num only [Fintype.card_perm,Fintype.card_fin,Nat.factorial] at h
  simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.mul_comm] using h.symm

private noncomputable def fixedCard (p : Equiv.Perm (Fin 4)) : Fin 5 :=
  ⟨Fintype.card {c : Fin 4 // p c=c}, by
    have h := Fintype.card_subtype_le (fun c : Fin 4 => p c=c)
    simp only [Fintype.card_fin] at h
    omega⟩

private theorem permutation_sum (f : Fin 5 → ℕ) :
    (∑ p : Equiv.Perm (Fin 4), f (fixedCard p)) =
      9*f 0 + 8*f 1 + 6*f 2 + f 4 := by
  classical
  have hc (r : Fin 5) :
      (Finset.univ.filter (fun p : Equiv.Perm (Fin 4) => fixedCard p=r)).card =
        (![9,8,6,0,1] : Fin 5 → ℕ) r := by
    revert r
    decide +kernel
  calc
    _ = ∑ p : Equiv.Perm (Fin 4), ∑ r : Fin 5,
        if fixedCard p=r then f r else 0 := by simp
    _ = ∑ r : Fin 5, ∑ p : Equiv.Perm (Fin 4),
        if fixedCard p=r then f r else 0 := Finset.sum_comm
    _ = ∑ r : Fin 5, (![9,8,6,0,1] : Fin 5 → ℕ) r * f r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter, Finset.sum_const, hc, smul_eq_mul]
    _ = _ := by simp [Fin.sum_univ_succ]; ring

private def edge_path (n : ℕ) : Edge n 1 ≃ Fin (n-1) where
  toFun
    | .H _ j => Fin.elim0 j
    | .V i _ => i
    | .D _ j => Fin.elim0 j
    | .A _ j => Fin.elim0 j
  invFun i := .V i 0
  left_inv e := by
    cases e with
    | H i j => exact Fin.elim0 j
    | V i j => exact congrArg (Edge.V i) (Subsingleton.elim _ _)
    | D i j => exact Fin.elim0 j
    | A i j => exact Fin.elim0 j
  right_inv _ := rfl

private theorem oneDefect_path {n : ℕ} (f : Fin n → Fin 4) :
    OneDefect (fun p : Cell n 1 => f p.1) ↔ bad f=1 := by
  classical
  unfold OneDefect
  have h : (Finset.univ.filter (mono (fun p : Cell n 1 => f p.1))).card = bad f := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← (edge_path n).symm.sum_comp]
    rfl
  rw [h]

private theorem normal_path {n : ℕ} (f : Fin n → Fin 4) :
    normal (fun p : Cell n 1 => f p.1) ↔ Canonical f := by
  simp only [normal,Canonical]
  constructor
  · intro h i b hb
    obtain ⟨j,hj,he⟩ := h (finProdFinEquiv (i,0)) b (by simpa using hb)
    refine ⟨(finProdFinEquiv.symm j).1,?_,he⟩
    change (finProdFinEquiv.symm j).1.val < i.val
    simpa [Fin.lt_def, finProdFinEquiv, Fin.divNat] using hj
  · intro h i b hb
    obtain ⟨j,hj,he⟩ := h (finProdFinEquiv.symm i).1 b hb
    refine ⟨finProdFinEquiv (j,0),?_,by simpa using he⟩
    change (finProdFinEquiv (j,0)).val < i.val
    simpa [Fin.lt_def, finProdFinEquiv, Fin.divNat] using hj

private noncomputable def literal_words (n : ℕ) :
    {f : Cell n 1 → Fin 4 // OneDefect f ∧ normal f} ≃
      {f : Fin n → Fin 4 // bad f=1 ∧ Canonical f} where
  toFun f := ⟨(fun i => f.val (i,0)), by
    have he : (fun p : Cell n 1 => f.val (p.1,0)) = f.val := by
      funext p; exact congrArg f.val (Prod.ext rfl (Subsingleton.elim _ _))
    exact ⟨(oneDefect_path _).mp (he.symm ▸ f.property.1),
      (normal_path _).mp (he.symm ▸ f.property.2)⟩⟩
  invFun f := ⟨(fun p => f.val p.1),
    (oneDefect_path _).mpr f.property.1,(normal_path _).mpr f.property.2⟩
  left_inv f := by
    apply Subtype.ext; funext p
    exact congrArg f.val (Prod.ext rfl (Subsingleton.elim _ _))
  right_inv _ := rfl

private theorem literal_count (n : ℕ) :
    T n 1 = Nat.card {f : Fin n → Fin 4 // bad f=1 ∧ Canonical f} := by
  classical
  rw [show T n 1 = Nat.card {f : Cell n 1 → Fin 4 // OneDefect f ∧ normal f} by
    simp [T,Nat.card_eq_fintype_card,Fintype.card_subtype]]
  exact Nat.card_congr (literal_words n)

theorem width_one_large (n : ℕ) (hn : 3 ≤ n) :
    54*(T n 1 : ℤ) = ((n : ℤ)-1)*3^n+27*((n : ℤ)-1) := by
  classical
  obtain ⟨m,rfl⟩ : ∃ m, n=m+3 := ⟨n-3,by omega⟩
  have h := burnside (m+3)
  rw [← literal_count] at h
  have hf (p : Equiv.Perm (Fin 4)) :
      Nat.card (MulAction.fixedBy (Words (m+3)) p) =
        (fixedCard p).val*(m+2)*((fixedCard p).val-1)^(m+1) := by
    rw [Nat.card_congr (fixed_words (m+3) p)]
    exact path_count (m+2)
  simp_rw [hf] at h
  rw [permutation_sum (fun r : Fin 5 => r.val*(m+2)*(r.val-1)^(m+1))] at h
  norm_num at h
  have h' := congrArg (fun x : ℕ => (x : ℤ)) h
  push_cast at h' ⊢
  simp only [pow_succ] at h' ⊢
  nlinarith [h']

#check @width_one_large
#print axioms width_one_large
end D5.S3.StatisticalMechanics.Potts.KingDefects.KingPath
