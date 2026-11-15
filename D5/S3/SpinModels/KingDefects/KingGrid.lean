/- GID: D5/S3/SpinModels/KingDefects/KingGrid
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Literal king-grid colourings and decomposition by the unique defective edge. -/
/-
admission_basis: escape-witness
escape_witness: defectEquiv (extracting the unique defective edge).
The declarations describe finite families uniformly in both dimensions; no bounded
enumeration, checker, numerical reduction or certified instance is asserted.
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.Rev

/-! Literal edges, restricted-growth words and their finite families. -/
namespace D5.S3.SpinModels.KingDefects.KingGrid

abbrev Cell (n k : ℕ) := Fin n × Fin k

inductive Edge (n k : ℕ)
  | H (i : Fin n) (j : Fin (k-1))
  | V (i : Fin (n-1)) (j : Fin k)
  | D (i : Fin (n-1)) (j : Fin (k-1))
  | A (i : Fin (n-1)) (j : Fin (k-1))
  deriving DecidableEq, Fintype

def lo {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val, by omega⟩
def hi {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val+1, by omega⟩

def end0 {n k : ℕ} : Edge n k → Cell n k
  | .H i j => (i, lo j)
  | .V i j => (lo i, j)
  | .D i j => (lo i, lo j)
  | .A i j => (lo i, hi j)

def end1 {n k : ℕ} : Edge n k → Cell n k
  | .H i j => (i, hi j)
  | .V i j => (hi i, j)
  | .D i j => (hi i, hi j)
  | .A i j => (hi i, lo j)

abbrev mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) : Prop :=
  f (end0 e) = f (end1 e)

def OneDefect {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) : Prop :=
  (Finset.univ.filter (mono f)).card = 1

def DefectAt {n k : ℕ} {C : Type*} (e : Edge n k) (f : Cell n k → C) : Prop :=
  ∀ d, mono f d ↔ d = e

/-- The order on the flattened word is precisely row-major order. -/
def normal {n k : ℕ} (f : Cell n k → Fin 4) : Prop :=
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
    (fun i : Fin (n*k) => f (finProdFinEquiv.symm i))

noncomputable def L (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f)).card

noncomputable def T (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Cell n k → Fin 4 => OneDefect f ∧ normal f)).card

theorem oneDefect_iff {n k : ℕ} {C : Type*} [DecidableEq C] (f : Cell n k → C) :
    OneDefect f ↔ ∃! e, mono f e := by
  simp [OneDefect, Finset.card_eq_one_iff_existsUnique]

theorem defectAt_iff {n k : ℕ} {C : Type*} [DecidableEq C]
    (e : Edge n k) (f : Cell n k → C) :
    DefectAt e f ↔ OneDefect f ∧ mono f e := by
  rw [oneDefect_iff]
  constructor
  · intro h
    exact ⟨⟨e, (h e).mpr rfl, fun d hd => (h d).mp hd⟩, (h e).mpr rfl⟩
  · rintro ⟨⟨d, hd, hu⟩, he⟩ a
    exact ⟨fun ha => (hu a ha).trans (hu e he).symm, fun ha => ha ▸ he⟩

noncomputable def defectEquiv {n k : ℕ} {C : Type*} [DecidableEq C] :
    {f : Cell n k → C // OneDefect f} ≃ Σ e : Edge n k, {f : Cell n k → C // DefectAt e f} where
  toFun f := by
    let e := Classical.choose ((oneDefect_iff f.val).mp f.property)
    have he := Classical.choose_spec ((oneDefect_iff f.val).mp f.property)
    exact ⟨e, f.val, (defectAt_iff e f.val).mpr ⟨f.property, he.1⟩⟩
  invFun q := ⟨q.2.val, ((defectAt_iff q.1 q.2.val).mp q.2.property).1⟩
  left_inv f := Subtype.ext rfl
  right_inv q := by
    apply Sigma.subtype_ext
    · exact (q.2.property _).mp
        (Classical.choose_spec ((oneDefect_iff q.2.val).mp
          ((defectAt_iff q.1 q.2.val).mp q.2.property).1)).1
    · rfl

theorem labelled_count {n k : ℕ} : L n k = Nat.card {f : Cell n k → Fin 4 // OneDefect f} := by
  classical
  simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem count_by_edge (n k : ℕ) :
    L n k = ∑ e : Edge n k, Nat.card {f : Cell n k → Fin 4 // DefectAt e f} := by
  classical
  rw [labelled_count, Nat.card_congr (defectEquiv (n := n) (k := k))]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma]

/-- Transpose acts on edge types as H↔V, fixing the two diagonal types. -/
def transposeEdge {n k : ℕ} : Edge n k ≃ Edge k n where
  toFun
    | .H i j => .V j i
    | .V i j => .H j i
    | .D i j => .D j i
    | .A i j => .A j i
  invFun
    | .H i j => .V j i
    | .V i j => .H j i
    | .D i j => .D j i
    | .A i j => .A j i
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e <;> rfl

def transpose {n k : ℕ} {C : Type*} (f : Cell n k → C) : Cell k n → C :=
  fun p => f (p.2,p.1)

theorem transpose_mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) :
    mono (transpose f) (transposeEdge e) ↔ mono f e := by
  cases e <;> simp [mono, transpose, transposeEdge, end0, end1, eq_comm]

def transposeDefectEquiv {n k : ℕ} {C : Type*} (e : Edge n k) :
    {f : Cell n k → C // DefectAt e f} ≃
      {f : Cell k n → C // DefectAt (transposeEdge e) f} where
  toFun f := ⟨transpose f.val, by
    intro d
    obtain ⟨a, rfl⟩ := transposeEdge.surjective d
    rw [transpose_mono, f.property, transposeEdge.injective.eq_iff]⟩
  invFun f := ⟨transpose f.val, by
    intro d
    have h := f.property (transposeEdge d)
    have he : transposeEdge (transposeEdge d) = d := by cases d <;> rfl
    rw [← transpose_mono f.val (transposeEdge d), he,
      transposeEdge.injective.eq_iff] at h
    exact h⟩
  left_inv f := Subtype.ext rfl
  right_inv f := Subtype.ext rfl


theorem endpoints_distinct {n k : ℕ} (e : Edge n k) : end0 e ≠ end1 e := by
  cases e <;> simp [end0, end1, lo, hi, Fin.ext_iff, Prod.mk.injEq]

theorem edge_of_endpoints {n k : ℕ} (e d : Edge n k)
    (h0 : end0 e = end0 d) (h1 : end1 e = end1 d) : e = d := by
  cases e <;> cases d <;>
    simp_all [end0, end1, lo, hi, Fin.ext_iff, Prod.mk.injEq] <;>
      first | omega | (congr 1 <;> simp_all [Fin.ext_iff] <;> omega)

theorem endpoints_not_reversed {n k : ℕ} (e d : Edge n k) :
    ¬ (end0 e = end1 d ∧ end1 e = end0 d) := by
  cases e <;> cases d <;>
    simp [end0, end1, lo, hi, Fin.ext_iff, Prod.mk.injEq] <;> omega

/-- Reflection reverses H endpoints and exchanges D with A. -/
def reflectEdge {n k : ℕ} : Edge n k ≃ Edge n k where
  toFun
    | .H i j => .H i j.rev
    | .V i j => .V i j.rev
    | .D i j => .A i j.rev
    | .A i j => .D i j.rev
  invFun
    | .H i j => .H i j.rev
    | .V i j => .V i j.rev
    | .D i j => .A i j.rev
    | .A i j => .D i j.rev
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

def reflect {n k : ℕ} {C : Type*} (f : Cell n k → C) : Cell n k → C :=
  fun p => f (p.1,p.2.rev)

private theorem rev_lo {n : ℕ} (i : Fin (n-1)) : (lo i).rev = hi i.rev := by
  apply Fin.ext
  dsimp [lo, hi, Fin.rev]
  omega

private theorem rev_hi {n : ℕ} (i : Fin (n-1)) : (hi i).rev = lo i.rev := by
  apply Fin.ext
  dsimp [lo, hi, Fin.rev]
  omega

theorem reflect_mono {n k : ℕ} {C : Type*} (f : Cell n k → C) (e : Edge n k) :
    mono (reflect f) (reflectEdge e) ↔ mono f e := by
  cases e <;> simp [mono, reflect, reflectEdge, end0, end1, rev_lo, rev_hi, eq_comm]

def reflectDefectEquiv {n k : ℕ} {C : Type*} (e : Edge n k) :
    {f : Cell n k → C // DefectAt e f} ≃
      {f : Cell n k → C // DefectAt (reflectEdge e) f} where
  toFun f := ⟨reflect f.val, by
    intro d
    obtain ⟨a,rfl⟩ := reflectEdge.surjective d
    rw [reflect_mono, f.property, reflectEdge.injective.eq_iff]⟩
  invFun f := ⟨reflect f.val, by
    intro d
    have h := f.property (reflectEdge d)
    have he : reflectEdge (reflectEdge d) = d := by cases d <;> simp [reflectEdge]
    rw [← reflect_mono f.val (reflectEdge d), he, reflectEdge.injective.eq_iff] at h
    exact h⟩
  left_inv f := by apply Subtype.ext; funext p; simp [reflect]
  right_inv f := by apply Subtype.ext; funext p; simp [reflect]


def UsesThree {X : Type*} (f : X → Fin 4) : Prop :=
  ∃ a b c, f a ≠ f b ∧ f a ≠ f c ∧ f b ≠ f c

private theorem perm_ext_three {X : Type*} (f : X → Fin 4) (hf : UsesThree f)
    (p q : Equiv.Perm (Fin 4)) (h : p ∘ f = q ∘ f) : p = q := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hf
  have he (t : X) : p (f t) = q (f t) := congrFun h t
  ext x
  by_cases ha : x = f a
  · simpa [ha] using he a
  by_cases hb : x = f b
  · simpa [hb] using he b
  by_cases hc : x = f c
  · simpa [hc] using he c
  by_contra hn
  have hcard : ({p (f a),p (f b),p (f c),p x,q x} : Finset (Fin 4)).card ≤ 4 := by
    simpa using (Finset.card_le_card
      (Finset.subset_univ ({p (f a),p (f b),p (f c),p x,q x} : Finset (Fin 4))))
  have hpa : p (f a) ≠ q x := by rw [he a]; exact q.injective.ne ha.symm
  have hpb : p (f b) ≠ q x := by rw [he b]; exact q.injective.ne hb.symm
  have hpc : p (f c) ≠ q x := by rw [he c]; exact q.injective.ne hc.symm
  simp [Finset.card_insert_of_notMem, p.injective.ne hab, p.injective.ne hac,
    p.injective.ne hbc, p.injective.ne ha.symm, p.injective.ne hb.symm,
    p.injective.ne hc.symm, hpa, hpb, hpc, hn] at hcard

private theorem canonical_count_three {X : Type*} [Fintype X] [LinearOrder X]
    (S : (X → Fin 4) → Prop)
    (hinv : ∀ p : Equiv.Perm (Fin 4), ∀ f, S (p ∘ f) ↔ S f)
    (hthree : ∀ f, S f → UsesThree f) :
    Nat.card {f // S f} = 24 * Nat.card {f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} := by
  classical
  let E : ({f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} ×
      Equiv.Perm (Fin 4)) → {f // S f} :=
    fun q => ⟨q.2 ∘ q.1.val, (hinv q.2 q.1.val).mpr q.1.property.1⟩
  have hE : Function.Bijective E := by
    constructor
    · rintro ⟨Q,p⟩ ⟨R,q⟩ h
      have he : p ∘ Q.val = q ∘ R.val := congrArg Subtype.val h
      obtain ⟨U, hU, hu⟩ :=
        D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique
          (p ∘ Q.val)
      have hQ : Q.val = U := hu _ ⟨Q.property.2,p.symm, by ext i; simp⟩
      have hR : R.val = U := hu _ ⟨R.property.2,q.symm, by rw [he]; ext i; simp⟩
      have hs : Q = R := Subtype.ext (hQ.trans hR.symm)
      subst R
      exact Prod.ext rfl (perm_ext_three Q.val (hthree _ Q.property.1) p q he)
    · intro P
      obtain ⟨Q,⟨hQ,p,hp⟩,_⟩ :=
        D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique P.val
      have hS : S Q := hp ▸ (hinv p P.val).mpr P.property
      refine ⟨(⟨Q,hS,hQ⟩,p.symm), ?_⟩
      apply Subtype.ext
      funext i
      change p.symm (Q i) = P.val i
      rw [hp]
      exact p.symm_apply_apply _
  have hc := Nat.card_congr (Equiv.ofBijective E hE)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)),
    Fintype.card_perm, Fintype.card_fin] at hc
  norm_num at hc
  simpa only [Nat.mul_comm] using hc.symm

private theorem oneDefect_usesThree {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k)
    (f : Cell n k → Fin 4) (hf : OneDefect f) : UsesThree f := by
  let r0 : Fin n := ⟨0,by omega⟩
  let r1 : Fin n := ⟨1,by omega⟩
  let c0 : Fin k := ⟨0,by omega⟩
  let c1 : Fin k := ⟨1,by omega⟩
  let ri : Fin (n-1) := ⟨0,by omega⟩
  let ci : Fin (k-1) := ⟨0,by omega⟩
  obtain ⟨e,he,hu⟩ := (oneDefect_iff f).mp hf
  have unique {d a : Edge n k} (hd : mono f d) (ha : mono f a) : d = a :=
    (hu d hd).trans (hu a ha).symm
  by_cases hab : f (r0,c0) = f (r0,c1)
  · have htop : mono f (.H r0 ci) := hab
    refine ⟨(r0,c0),(r1,c0),(r1,c1),?_,?_,?_⟩
    · intro h
      have heq := unique htop (show mono f (.V ri c0) from h)
      cases heq
    · intro h
      have heq := unique htop (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique htop (show mono f (.H r1 ci) from h)
      have hrow := congrArg Fin.val (Edge.H.inj heq).1
      norm_num [r0,r1] at hrow
  by_cases hac : f (r0,c0) = f (r1,c0)
  · have hleft : mono f (.V ri c0) := hac
    refine ⟨(r0,c0),(r0,c1),(r1,c1),hab,?_,?_⟩
    · intro h
      have heq := unique hleft (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique hleft (show mono f (.V ri c1) from h)
      have hcol := congrArg Fin.val (Edge.V.inj heq).2
      norm_num [c0,c1] at hcol
  by_cases hbc : f (r0,c1) = f (r1,c0)
  · have hanti : mono f (.A ri ci) := hbc
    refine ⟨(r0,c0),(r0,c1),(r1,c1),hab,?_,?_⟩
    · intro h
      have heq := unique hanti (show mono f (.D ri ci) from h)
      cases heq
    · intro h
      have heq := unique hanti (show mono f (.V ri c1) from h)
      cases heq
  exact ⟨(r0,c0),(r0,c1),(r1,c0),hab,hac,hbc⟩

/-- Three occurring colours already make the four-colour permutation action free. -/
theorem labelled_eq_twentyFour (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    L n k = 24 * T n k := by
  classical
  let word (f : Fin (n*k) → Fin 4) : Cell n k → Fin 4 := fun p => f (finProdFinEquiv p)
  let S (f : Fin (n*k) → Fin 4) := OneDefect (word f)
  have hinv : ∀ p : Equiv.Perm (Fin 4), ∀ f, S (p ∘ f) ↔ S f := by
    intro p f
    simp only [S, word, OneDefect, mono, Function.comp_apply, p.injective.eq_iff]
  have huse : ∀ f, S f → UsesThree f := by
    intro f hf
    obtain ⟨a,b,c,hab,hac,hbc⟩ := oneDefect_usesThree hn hk (word f) hf
    exact ⟨finProdFinEquiv a,finProdFinEquiv b,finProdFinEquiv c,hab,hac,hbc⟩
  have h := canonical_count_three S hinv huse
  let E : (Cell n k → Fin 4) ≃ (Fin (n*k) → Fin 4) :=
    Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)
  have hL : L n k = Nat.card {f // S f} := by
    rw [labelled_count]
    exact Nat.card_congr (E.subtypeEquiv (by intro f; simp [E,S,word,OneDefect]))
  have hT : T n k = Nat.card {f // S f ∧
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical f} := by
    rw [show T n k = Nat.card {f : Cell n k → Fin 4 // OneDefect f ∧ normal f} by
      simp [T,Nat.card_eq_fintype_card,Fintype.card_subtype]]
    exact Nat.card_congr (E.subtypeEquiv (by intro f; simp [E,S,word,normal,OneDefect]))
  rw [hL,hT]
  exact h

end D5.S3.SpinModels.KingDefects.KingGrid
