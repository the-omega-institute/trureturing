/- GID: D5/S3/Combinatorics/MatrixOrbits/TwistedOrbits
   generality: G
   mirror-B: none(waiver:covered-by-symmetric-representative-series-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Twisted orbits of four by four matrices. -/

import OmegaBuild.Commands
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

compile_only_with_mathlib

/-! # Twisted orbits of four by four matrices.

The ambient action permutes rows and columns independently. A finite
position calculation turns a transpose-fixed orbit into one with a
symmetric representative. The twisted orbit count then reduces to the
five conjugacy classes of permutations of four labels.
-/

open scoped BigOperators
open MulAction

namespace A333886

abbrev I := Fin 4
abbrev P := Equiv.Perm I
private abbrev Mat := I → I → ℕ

private def step (p : P) (ij : I × I) : I × I := (ij.2, p ij.1)

private def Twist (p : P) (A : Mat) : Prop :=
  ∀ i j, A i j = A j (p i)

private def Symmetric (A : Mat) : Prop := ∀ i j, A i j = A j i

private def Relabel (p q : P) (A : Mat) : Mat := fun i j => A (p i) (q j)

private def Transpose (A : Mat) : Mat := fun i j => A j i

private theorem symmetrizer_certificate :
    ∀ p : P, ∃ q : P, ∀ i j : I, ∃ k : Fin 16,
      (step p)^[k.val] (i, q j) = (j, q i) := by
  decide +kernel

private theorem transport_along_steps (p : P) {A : Mat} (h : Twist p A) (k : ℕ) (ij : I × I) :
    A ij.1 ij.2 = A ((step p)^[k] ij).1 ((step p)^[k] ij).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (h _ _)

private theorem symmetrize_twist {p : P} {A : Mat} (h : Twist p A) :
    ∃ q : P, Symmetric (Relabel 1 q A) := by
  obtain ⟨q, hq⟩ := symmetrizer_certificate p
  refine ⟨q, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := hq i j
  change A i (q j) = A j (q i)
  simpa only [hk] using transport_along_steps p h k (i, q j)

private theorem transpose_fixed_iff_symmetric_representative (A : Mat) :
    (∃ p q : P, Relabel p q (Transpose A) = A) ↔
    (∃ p q : P, Symmetric (Relabel p q A)) := by
  constructor
  · rintro ⟨p,q,h⟩
    have he : ∀ i j, A i j = A (q j) (p i) :=
      fun i j => (congrFun (congrFun h i) j).symm
    have ht : Twist (p * q) (Relabel q 1 A) := by
      intro i j
      exact he (q i) j
    obtain ⟨r, hr⟩ := symmetrize_twist ht
    exact ⟨q,r,hr⟩
  · rintro ⟨p,q,h⟩
    refine ⟨q * p.symm, p * q.symm, ?_⟩
    funext i j
    have h' := h (p.symm i) (q.symm j)
    simpa [Relabel, Transpose, Equiv.Perm.mul_apply] using h'.symm

section TwistedBurnside
universe u
variable {G X : Type u} [Group G] [MulAction G X]

private abbrev OrbitQuotient (G X : Type*) [Group G] [MulAction G X] :=
  Quotient (MulAction.orbitRel G X)

private def stabilizerTransport {x y : X} (g : G) (hg : g • y = x) :
    {h : G // h • y = x} ≃ MulAction.stabilizer G x where
  toFun h := ⟨h.val * g⁻¹, by
    change (h.val * g⁻¹) • x = x
    have hh := h.property
    rw [mul_smul, show g⁻¹ • x = y by rw [← hg, inv_smul_smul]]
    exact hh⟩
  invFun h := ⟨h.val * g, by
    rw [mul_smul, hg]
    exact h.property⟩
  left_inv h := Subtype.ext (by simp)
  right_inv h := Subtype.ext (by simp)

private abbrev FixedOrbits (τ : X → X) :=
  {ω : OrbitQuotient G X // ∃ g : G, g • τ ω.out = ω.out}

private noncomputable def twistedFiberEquiv (τ : X → X) (φ : G → G)
    (hτ : ∀ g x, τ (g • x) = φ g • τ x) :
    (Σ g : G, {x : X // g • τ x = x}) ≃ FixedOrbits (G := G) τ × G := by
  classical
  have transfer (a b : X) (hb : b ∈ orbit G a) :
      (∃ g : G, g • τ b = b) ↔ ∃ g : G, g • τ a = a := by
    obtain ⟨r, hr⟩ := hb
    subst b
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨r⁻¹ * g * φ r, ?_⟩
      rw [mul_smul, mul_smul, ← hτ, hg, inv_smul_smul]
    · rintro ⟨g, hg⟩
      refine ⟨r * g * (φ r)⁻¹, ?_⟩
      rw [hτ, mul_smul, inv_smul_smul, mul_smul, hg]
  have restrict :
      (Σ ω : OrbitQuotient G X, Σ b : orbit G ω.out, {g : G // g • τ b.val = b.val}) ≃
        (Σ ω : FixedOrbits (G := G) τ,
          Σ b : orbit G ω.val.out, {g : G // g • τ b.val = b.val}) := by
    let h (ω : OrbitQuotient G X) (b : orbit G ω.out) (g : {g : G // g • τ b.val = b.val}) :=
      (transfer _ _ b.property).mp ⟨g, g.property⟩
    exact
      { toFun := fun ⟨ω, b, g⟩ => ⟨⟨ω, h ω b g⟩, b, g⟩
        invFun := fun ⟨ω, b, g⟩ => ⟨ω.val, b, g⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  calc
    (Σ g : G, {x : X // g • τ x = x}) ≃ {ab : G × X // ab.1 • τ ab.2 = ab.2} :=
      (Equiv.subtypeProdEquivSigmaSubtype (fun (g : G) (x : X) => g • τ x = x)).symm
    _ ≃ {ba : X × G // ba.2 • τ ba.1 = ba.1} :=
      (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ (Σ b : X, {g : G // g • τ b = b}) :=
      Equiv.subtypeProdEquivSigmaSubtype (fun (x : X) (g : G) => g • τ x = x)
    _ ≃ (Σ ωb : Σ ω : OrbitQuotient G X, orbit G ω.out,
        {g : G // g • τ ωb.2.val = ωb.2.val}) :=
      (selfEquivSigmaOrbits G X).sigmaCongrLeft'
    _ ≃ (Σ ω : OrbitQuotient G X,
        Σ b : orbit G ω.out, {g : G // g • τ b.val = b.val}) :=
      Equiv.sigmaAssoc (fun (ω : OrbitQuotient G X) (b : orbit G ω.out) => {g : G // g • τ b.val = b.val})
    _ ≃ (Σ ω : FixedOrbits (G := G) τ,
        Σ b : orbit G ω.val.out, {g : G // g • τ b.val = b.val}) := restrict
    _ ≃ (Σ ω : FixedOrbits (G := G) τ,
        Σ b : orbit G ω.val.out, MulAction.stabilizer G b.val) :=
      Equiv.sigmaCongrRight fun ω =>
        Equiv.sigmaCongrRight fun b =>
          let witness := (transfer _ _ b.property).mpr ω.property
          stabilizerTransport (Classical.choose witness) (Classical.choose_spec witness)
    _ ≃ (Σ ω : FixedOrbits (G := G) τ,
        Σ _ : orbit G ω.val.out, MulAction.stabilizer G ω.val.out) :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun b => (stabilizerEquivStabilizerOfOrbitRel b.property).toEquiv
    _ ≃ (Σ ω : FixedOrbits (G := G) τ, orbit G ω.val.out × MulAction.stabilizer G ω.val.out) :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ (Σ _ : FixedOrbits (G := G) τ, G) :=
      Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup G ω.val.out
    _ ≃ FixedOrbits (G := G) τ × G := Equiv.sigmaEquivProd _ _

end TwistedBurnside

def Margins (n : ℕ) (A : Mat) : Prop :=
  (∀ i, ∑ j, A i j = n) ∧ (∀ j, ∑ i, A i j = n)

abbrev Margin (n : ℕ) := {A : Mat // Margins n A}

private lemma entry_le_margin {n : ℕ} (A : Margin n) (i j : I) : A.val i j ≤ n := by
  refine le_trans (Finset.single_le_sum (f := A.val i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) ?_
  exact (A.property.1 i).le

instance (n : ℕ) : Finite (Margin n) :=
  Finite.of_injective (β := I → I → Fin (n+1))
    (fun A i j => ⟨A.val i j, Nat.lt_succ_of_le (entry_le_margin A i j)⟩)
    (fun _ _ h => Subtype.ext (funext fun i => funext fun j =>
      congrArg Fin.val (congrFun (congrFun h i) j)))

private lemma relabel_margins {n : ℕ} (A : Margin n) (p q : P) : Margins n (Relabel p q A.val) := by
  constructor
  · intro i
    exact (Equiv.sum_comp q (A.val (p i))).trans (A.property.1 (p i))
  · intro j
    exact (Equiv.sum_comp p (fun i => A.val i (q j))).trans (A.property.2 (q j))

instance (n : ℕ) : MulAction (P × P) (Margin n) where
  smul g A := ⟨Relabel g.1.symm g.2.symm A.val, relabel_margins A _ _⟩
  one_smul A := rfl
  mul_smul g h A := by
    apply Subtype.ext
    funext i j
    rfl

private def transposeMargin {n : ℕ} (A : Margin n) : Margin n :=
  ⟨Transpose A.val, A.property.2, A.property.1⟩

private def swapPerms (g : P × P) : P × P := (g.2, g.1)

private lemma transpose_smul {n : ℕ} (g : P × P) (A : Margin n) :
    transposeMargin (g • A) = swapPerms g • transposeMargin A := rfl

abbrev Orbit (n : ℕ) := OrbitQuotient (P × P) (Margin n)

private def SymmetricClasses (n : ℕ) :=
  {ω : Orbit n // ∃ p q : P, Symmetric (Relabel p q ω.out.val)}

instance (n : ℕ) : Finite (SymmetricClasses n) := by
  unfold SymmetricClasses
  infer_instance

noncomputable def a333886 (n : ℕ) : ℕ := Nat.card (SymmetricClasses n)

private noncomputable def symmetricClassesEquiv (n : ℕ) :
    FixedOrbits (G := P × P) (transposeMargin (n := n)) ≃ SymmetricClasses n := by
  refine (Equiv.refl (Orbit n)).subtypeEquiv fun ω => ?_
  change (∃ g : P × P, g • transposeMargin ω.out = ω.out) ↔
    ∃ p q : P, Symmetric (Relabel p q ω.out.val)
  rw [← transpose_fixed_iff_symmetric_representative]
  constructor
  · rintro ⟨⟨p,q⟩,h⟩
    exact ⟨p.symm,q.symm,congrArg Subtype.val h⟩
  · rintro ⟨p,q,h⟩
    exact ⟨(p.symm,q.symm),Subtype.ext h⟩

abbrev TwistMat (p : P) (n : ℕ) := {A : Margin n // Twist p A.val}

private noncomputable def twistPairEquiv {n : ℕ} (g : P × P) :
    {A : Margin n // g • transposeMargin A = A} ≃ TwistMat (g.1.symm * g.2.symm) n := by
  let e : Margin n ≃ Margin n :=
    { toFun := fun A => ⟨Relabel g.2.symm 1 A.val, relabel_margins A _ _⟩
      invFun := fun A => ⟨Relabel g.2 1 A.val, relabel_margins A _ _⟩
      left_inv := fun A => Subtype.ext (by funext i j; simp [Relabel])
      right_inv := fun A => Subtype.ext (by funext i j; simp [Relabel]) }
  refine e.subtypeEquiv fun A => ?_
  change g • transposeMargin A = A ↔
    ∀ i j, A.val (g.2.symm i) j = A.val (g.2.symm j) (g.1.symm (g.2.symm i))
  constructor
  · intro h i j
    exact (congrFun (congrFun (congrArg Subtype.val h) (g.2.symm i)) j).symm
  · intro h
    apply Subtype.ext
    funext i j
    change A.val (g.2.symm j) (g.1.symm i) = A.val i j
    have h' := (h (g.2 i) j).symm
    simpa only [Equiv.symm_apply_apply] using h'

def rep0 : P where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

def rep1 : P where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide
  right_inv := by decide

def rep2 : P where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

def rep3 : P where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide
  right_inv := by decide

def rep4 : P where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

def rep (k : Fin 5) : P := ![rep0, rep1, rep2, rep3, rep4] k

private def cycleIndex (p : P) : Fin 5 :=
  if p = 1 then 0
  else if p*p = 1 then
    if ∃ i : I, p i = i then 1 else 2
  else if ∃ i : I, p i = i then 3 else 4

def cycleMultiplicity (k : Fin 5) : ℕ := ![1, 6, 3, 8, 6] k

private lemma cycle_certificate : ∀ p : P, ∃ q : P, ∀ i : I,
    p (q i) = q (rep (cycleIndex p) i) := by decide +kernel

private lemma cycle_multiplicity_certificate : ∀ k : Fin 5,
    (Finset.univ.filter (fun p : P => cycleIndex p = k)).card = cycleMultiplicity k := by
  decide +kernel

structure TwistPattern (p : P) (k : ℕ) where
  label : I → I → Fin k
  pos : Fin k → I × I
  label_pos : ∀ u, label (pos u).1 (pos u).2 = u
  label_step : ∀ i j, label i j = label j (p i)
  reaches : ∀ i j, ∃ d : Fin 16, (step p)^[d.val] (pos (label i j)) = (i,j)

def pattern0 : TwistPattern rep0 10 where
  label i j := ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 5, 7, 8], ![3, 6, 8, 9]] i j
  pos := ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]
  label_pos := by decide +kernel
  label_step := by decide +kernel
  reaches := by decide +kernel

def pattern1 : TwistPattern rep1 6 where
  label i j := ![![0, 0, 1, 2], ![0, 0, 1, 2], ![1, 1, 3, 4], ![2, 2, 4, 5]] i j
  pos := ![(0,0), (0,2), (0,3), (2,2), (2,3), (3,3)]
  label_pos := by decide +kernel
  label_step := by decide +kernel
  reaches := by decide +kernel

def pattern2 : TwistPattern rep2 4 where
  label i j := ![![0, 0, 1, 2], ![0, 0, 2, 1], ![2, 1, 3, 3], ![1, 2, 3, 3]] i j
  pos := ![(0,0), (0,2), (0,3), (2,2)]
  label_pos := by decide +kernel
  label_step := by decide +kernel
  reaches := by decide +kernel

def pattern3 : TwistPattern rep3 4 where
  label i j := ![![0, 0, 1, 2], ![1, 0, 0, 2], ![0, 1, 0, 2], ![2, 2, 2, 3]] i j
  pos := ![(0,0), (0,2), (0,3), (3,3)]
  label_pos := by decide +kernel
  label_step := by decide +kernel
  reaches := by decide +kernel

def pattern4 : TwistPattern rep4 2 where
  label i j := ![![0, 0, 1, 1], ![1, 0, 0, 1], ![1, 1, 0, 0], ![0, 1, 1, 0]] i j
  pos := ![(0,0), (0,2)]
  label_pos := by decide +kernel
  label_step := by decide +kernel
  reaches := by decide +kernel

private noncomputable def rearrangePermPair : (P × P) ≃ (P × P) where
  toFun g := (g.1.symm * g.2.symm, g.2)
  invFun g := ((g.1 * g.2).symm, g.2)
  left_inv := by
    rintro ⟨p,q⟩
    change (((p⁻¹ * q⁻¹) * q)⁻¹, q) = (p,q)
    simp [mul_assoc]
  right_inv := by
    rintro ⟨p,q⟩
    change (((p * q)⁻¹)⁻¹ * q⁻¹, q) = (p,q)
    simp [mul_assoc]

private noncomputable def allTwistedPairsEquiv (n : ℕ) :
    (Σ g : P × P, {A : Margin n // g • transposeMargin A = A}) ≃
    (Σ g : P × P, TwistMat g.1 n) :=
  (Equiv.sigmaCongrRight fun g => twistPairEquiv g).trans (rearrangePermPair.symm.sigmaCongrLeft' (β := fun g => TwistMat g.1 n)).symm

private lemma sum_twist_card (n : ℕ) :
    (∑ p : P, Nat.card (TwistMat p n)) = 24 * a333886 n := by
  classical
  have hc := Nat.card_congr ((allTwistedPairsEquiv n).symm.trans
    ((twistedFiberEquiv transposeMargin swapPerms transpose_smul).trans
      (Equiv.prodCongr (symmetricClassesEquiv n) (Equiv.refl _))))
  have hp : Nat.card P = 24 := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  rw [Nat.card_sigma, Nat.card_prod, Nat.card_prod, hp, Fintype.sum_prod_type] at hc
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    hp, nsmul_eq_mul] at hc
  rw [← Finset.mul_sum] at hc
  change 24 * (∑ p : P, Nat.card (TwistMat p n)) = a333886 n * (24 * 24) at hc
  calc
    _ = (24 * (∑ p : P, Nat.card (TwistMat p n))) / 24 := by omega
    _ = (a333886 n * (24 * 24)) / 24 := by rw [hc]
    _ = _ := by omega

private def twistCongr {p r : P} {n : ℕ} (q : P) (h : ∀ i : I, p (q i) = q (r i)) :
    TwistMat p n ≃ TwistMat r n := by
  let e : Margin n ≃ Margin n :=
    { toFun := fun A => ⟨Relabel q q A.val, relabel_margins A q q⟩
      invFun := fun A => ⟨Relabel q.symm q.symm A.val, relabel_margins A _ _⟩
      left_inv := fun A => Subtype.ext (by funext i j; simp [Relabel])
      right_inv := fun A => Subtype.ext (by funext i j; simp [Relabel]) }
  refine e.subtypeEquiv fun A => ?_
  change Twist p A.val ↔ Twist r (Relabel q q A.val)
  constructor
  · intro ht i j
    exact (ht (q i) (q j)).trans (by rw [h]; rfl)
  · intro ht i j
    have ht' := ht (q.symm i) (q.symm j)
    simpa only [Relabel, ← h, Equiv.apply_symm_apply] using ht'

lemma cycle_count (n : ℕ) :
    (∑ k : Fin 5, cycleMultiplicity k * Nat.card (TwistMat (rep k) n)) = 24 * a333886 n := by
  classical
  rw [← sum_twist_card]
  have hh (p : P) : Nat.card (TwistMat (rep (cycleIndex p)) n) = Nat.card (TwistMat p n) := by
    obtain ⟨q,h⟩ := cycle_certificate p
    exact Nat.card_congr (twistCongr q h).symm
  calc
    _ = ∑ k : Fin 5, ∑ p ∈ Finset.univ.filter (fun p : P => cycleIndex p = k),
        Nat.card (TwistMat (rep (cycleIndex p)) n) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← cycle_multiplicity_certificate]
      exact (Finset.sum_const_nat fun p hp => by rw [(Finset.mem_filter.mp hp).2]).symm
    _ = _ := by
      simp only [hh]
      exact Finset.sum_fiberwise Finset.univ cycleIndex _

def TwistPattern.rows {p : P} {k : ℕ} (pat : TwistPattern p k) (n : ℕ) (v : Fin k → ℕ) :
    Prop := ∀ i : I, ∑ j, v (pat.label i j) = n

def TwistPattern.equiv {p : P} {k : ℕ} (pat : TwistPattern p k) (n : ℕ) :
    TwistMat p n ≃ {v : Fin k → ℕ // pat.rows n v} := by
  have entry (A : TwistMat p n) (i j : I) :
      A.val.val (pat.pos (pat.label i j)).1 (pat.pos (pat.label i j)).2 = A.val.val i j := by
    obtain ⟨d, hd⟩ := pat.reaches i j
    simpa only [hd] using transport_along_steps p A.property d (pat.pos (pat.label i j))
  refine
    { toFun := fun A => ⟨fun u => A.val.val (pat.pos u).1 (pat.pos u).2, ?_⟩
      invFun := fun v => ⟨⟨fun i j => v.val (pat.label i j), v.property, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    simp only [entry]
    exact A.val.property.1 i
  · intro j
    have h := v.property (p.symm j)
    calc
      _ = ∑ i, v.val (pat.label (p.symm j) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pat.label_step, Equiv.apply_symm_apply]
      _ = _ := h
  · intro i j
    exact congrArg v.val (pat.label_step i j)
  · intro A
    exact Subtype.ext (Subtype.ext (funext fun i => funext fun j => entry A i j))
  · intro v
    exact Subtype.ext (funext fun u => congrArg v.val (pat.label_pos u))

-- Characterize the ambient equivalence directly by two independent permutations.
private lemma ambient_equivalence {n : ℕ} (A B : Margin n) :
    (Quotient.mk (MulAction.orbitRel (P × P) (Margin n)) A : Orbit n) =
        Quotient.mk _ B ↔ ∃ p q : P, Relabel p q A.val = B.val := by
  constructor
  · intro h
    have hr := Quotient.exact h.symm
    obtain ⟨⟨p,q⟩,hp⟩ := hr
    have ha : Relabel p.symm q.symm A.val = B.val := congrArg Subtype.val hp
    exact ⟨p.symm,q.symm,ha⟩
  · rintro ⟨p,q,h⟩
    symm
    apply Quotient.sound
    exact ⟨(p.symm,q.symm),Subtype.ext h⟩

abbrev sourceClasses (n : ℕ) :=
  {ω : Orbit n // ∃ B : Margin n, Quotient.mk _ B = ω ∧ Symmetric B.val}

def sourceClassesEquiv (n : ℕ) : SymmetricClasses n ≃ sourceClasses n := by
  refine (Equiv.refl (Orbit n)).subtypeEquiv fun ω => ?_
  have hOut : (Quotient.mk _ ω.out : Orbit n) = ω := Quotient.out_eq _
  change (∃ p q : P, Symmetric (Relabel p q ω.out.val)) ↔
    ∃ B : Margin n, Quotient.mk _ B = ω ∧ Symmetric B.val
  constructor
  · rintro ⟨p,q,h⟩
    let B : Margin n := ⟨Relabel p q ω.out.val, relabel_margins ω.out p q⟩
    refine ⟨B, ?_, h⟩
    rw [← hOut]
    exact ((ambient_equivalence ω.out B).mpr ⟨p,q,rfl⟩).symm
  · rintro ⟨B,hB,hs⟩
    obtain ⟨p,q,h⟩ := (ambient_equivalence ω.out B).mp (hOut.trans hB.symm)
    exact ⟨p,q,h.symm ▸ hs⟩

theorem four_rows {p : P} {k n : ℕ} (pat : TwistPattern p k) (v : Fin k → ℕ) :
    pat.rows n v ↔
      (∑ j : I, v (pat.label 0 j)) = n ∧
      (∑ j : I, v (pat.label 1 j)) = n ∧
      (∑ j : I, v (pat.label 2 j)) = n ∧
      (∑ j : I, v (pat.label 3 j)) = n := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3⟩
  · rintro ⟨h0,h1,h2,h3⟩ i
    fin_cases i <;> assumption

end A333886
