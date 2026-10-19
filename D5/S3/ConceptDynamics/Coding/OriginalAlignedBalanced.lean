/- GID: D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalAlignedBalanced
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original fixed-lag numbered-path alignment implies both balances for the same four bijections. -/

/- The proposal provenance below records the source's historical preparation.
   The mathematical declarations and proof terms are retained verbatim. -/
/-
Source proposal for BDR arXiv:2411.05598v1, Proposition 3.4.
The original tuple and the original fixed lag occur throughout.
This standalone artifact has NOT been elaborated or kernel checked.

Receiver: 1e0add864e162068a0543535f51dc9beb14bd4ba.
Terminal source: c1b069408db977a8f1902d26685a4328bf1ef7f1.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

The concatenate/word calculation below extracts the path-only calculation
from IncomingLiftAmbiguityCriterion.lean, proof-local concatenate_paths,
lines 663--683 at the receiver. It is proof organization, not new content.
The original project sources are Copyright The Omega Institute,
Apache-2.0. List concatenation laws and equivalence laws are reused.
-/
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
import D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
import D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
import Mathlib.Data.Sigma.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound (pathWord)

/- The cast changes only the natural length index. -/
private def lengthCast {n d e : ℕ} {A : CountMat n n}
    {i j : Fin n} (h : d = e) (p : FinitePath A d i j) :
    FinitePath A e i j := h ▸ p

private theorem word_lengthCast {n d e : ℕ} {A : CountMat n n}
    {i j : Fin n} (h : d = e) (p : FinitePath A d i j) :
    pathWord (lengthCast h p) = pathWord p := by
  cases h
  rfl

private abbrev Split {n : ℕ} (A : CountMat n n) (d e : ℕ)
    (i w : Fin n) :=
  Σ v : Fin n, FinitePath A d i v × FinitePath A e v w

/- Use the existing owner's complete supplier through the identity vertex lift. -/
private def identityLift {n : ℕ} (A : CountMat n n) : IncomingLift A (Fin n) where
  project := id
  onto i := ⟨i, rfl⟩
  lift a _ := ⟨a.source, rfl⟩

private def concatenate {n : ℕ} {A : CountMat n n}
    {d e : ℕ} {i j w : Fin n}
    (p : FinitePath A d i j) (q : FinitePath A e j w) :
    FinitePath A (d + e) i w :=
  Classical.choose (IncomingLiftAmbiguityCriterion.concatenate_paths (identityLift A) p q)

private theorem word_concatenate {n : ℕ} {A : CountMat n n}
    {d e : ℕ} {i j w : Fin n}
    (p : FinitePath A d i j) (q : FinitePath A e j w) :
    pathWord (concatenate p q) = pathWord p ++ pathWord q :=
  (Classical.choose_spec
    (IncomingLiftAmbiguityCriterion.concatenate_paths (identityLift A) p q)).1

/- Equal words with fixed start and length recover the dependent endpoint. -/
private theorem word_endpoint_injective {n : ℕ} {A : CountMat n n} :
    ∀ {d : ℕ} {i j j' : Fin n}
      (p : FinitePath A d i j) (q : FinitePath A d i j'),
      pathWord p = pathWord q →
      (⟨j, p⟩ : Σ v : Fin n, FinitePath A d i v) = ⟨j', q⟩ := by
  intro d i j j' p
  induction p generalizing j' with
  | nil i =>
      intro q h
      cases q with
      | nil _ => rfl
  | @cons d i v j a p ih =>
      intro q h
      cases q with
      | @cons _ _ v' _ a' q =>
          have hh : (⟨i, v, a⟩ : Edge A) = ⟨i, v', a'⟩ :=
            (List.cons.inj h).1
          have hv : v = v' := congrArg Edge.target hh
          subst v'
          have ha : a = a' :=
            Fin.ext (congrArg (fun x : Edge A => x.number.val) hh)
          subst a'
          have ht := ih q (List.cons.inj h).2
          have hj : j = j' := congrArg Sigma.fst ht
          subst j'
          have hp : p = q := sigma_mk_injective ht
          subst q
          rfl

/- At a fixed cut length, the whole word recovers the vertex and both paths. -/
private theorem split_word_injective {n : ℕ} {A : CountMat n n}
    (d e : ℕ) {i w : Fin n} (x y : Split A d e i w)
    (h : pathWord x.2.1 ++ pathWord x.2.2 =
      pathWord y.2.1 ++ pathWord y.2.2) : x = y := by
  induction d generalizing i with
  | zero =>
      rcases x with ⟨v, p, q⟩
      cases p with
      | nil i =>
          rcases y with ⟨v', p', q'⟩
          cases p' with
          | nil _ =>
              have hq : q = q' :=
                sigma_mk_injective (word_endpoint_injective q q' h)
              subst q'
              rfl
  | succ d ih =>
      rcases x with ⟨v, p, q⟩
      rcases y with ⟨v', p', q'⟩
      cases p with
      | @cons _ _ j _ a p =>
          cases p' with
          | @cons _ _ j' _ a' p' =>
              have hh : (⟨i, j, a⟩ : Edge A) = ⟨i, j', a'⟩ :=
                (List.cons.inj h).1
              have hj : j = j' := congrArg Edge.target hh
              subst j'
              have ha : a = a' :=
                Fin.ext (congrArg (fun x : Edge A => x.number.val) hh)
              subst a'
              have ht : (⟨v, p, q⟩ : Split A d e j w) = ⟨v', p', q'⟩ :=
                ih ⟨v, p, q⟩ ⟨v', p', q'⟩ (List.cons.inj h).2
              exact congrArg
                (fun c : Split A d e j w =>
                  (⟨c.1, FinitePath.cons a c.2.1, c.2.2⟩ :
                    Split A (d + 1) e i w)) ht

private def cut {n : ℕ} {A : CountMat n n} :
    (d e : ℕ) → {i w : Fin n} →
      FinitePath A (d + e) i w → Split A d e i w
  | 0, e, i, _, p => ⟨i, .nil i, lengthCast (Nat.zero_add e) p⟩
  | d + 1, e, _, _, p =>
      match lengthCast (Nat.succ_add d e) p with
      | .cons a tail =>
          let c := cut d e tail
          ⟨c.1, .cons a c.2.1, c.2.2⟩

private theorem word_cut {n : ℕ} {A : CountMat n n}
    (d e : ℕ) {i w : Fin n} (p : FinitePath A (d + e) i w) :
    pathWord (cut d e p).2.1 ++ pathWord (cut d e p).2.2 = pathWord p := by
  induction d generalizing i with
  | zero =>
      simp only [cut, pathWord, List.nil_append, word_lengthCast]
  | succ d ih =>
      cases hc : lengthCast (Nat.succ_add d e) p with
      | @cons _ _ j _ a tail =>
          have hw : pathWord p = pathWord (FinitePath.cons a tail) := by
            simpa only [word_lengthCast] using congrArg pathWord hc
          simp only [cut]
          erw [hc]
          change (⟨i, j, a⟩ : Edge A) ::
            (pathWord (cut d e tail).2.1 ++ pathWord (cut d e tail).2.2) = pathWord p
          rw [ih tail]
          exact hw.symm

private def concatenateEquiv {n : ℕ} (A : CountMat n n) (d e : ℕ)
    (i w : Fin n) : Split A d e i w ≃ FinitePath A (d + e) i w where
  toFun x := concatenate x.2.1 x.2.2
  invFun p := cut d e p
  left_inv := by
    intro x
    apply split_word_injective d e
    exact (word_cut d e (concatenate x.2.1 x.2.2)).trans
      (word_concatenate x.2.1 x.2.2)
  right_inv := by
    intro p
    have hw := (word_concatenate (cut d e p).2.1 (cut d e p).2.2).trans
      (word_cut d e p)
    exact sigma_mk_injective (word_endpoint_injective _ _ hw)

private theorem word_appendPath {n d : ℕ} {A : CountMat n n}
    {i j w : Fin n} (p : FinitePath A d i j) (a : Fin (A j w)) :
    pathWord (appendPath p a) = pathWord p ++ [⟨j, w, a⟩] := by
  induction p with
  | nil i => rfl
  | @cons d i j v b p ih =>
      simp only [appendPath, pathWord, List.cons_append, ih]

/-- Literal A alignment on actual numbered inputs, with the canonical cut. -/
def AlignedA {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w) : Prop :=
  ∀ {i j w : Fin n} {z : Fin k}
    (a : Fin (A i j)) (r : Fin (R j z)) (s : Fin (S z w)),
    let q := phiR i z ⟨j, a, r⟩
    let u := phiS q.1 w ⟨z, q.2.2, s⟩
    appendPath (psiA i u.1 ⟨q.1, q.2.1, u.2.1⟩) u.2.2 =
      FinitePath.cons a (psiA j w ⟨z, r, s⟩)

/-- Literal B alignment. The input middle vertex of phiR is j. -/
def AlignedB {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiB : ∀ t v, EdgePair S R t v ≃ FinitePath B m t v) : Prop :=
  ∀ {t z v : Fin k} {j : Fin n}
    (b : Fin (B t z)) (s : Fin (S z j)) (r : Fin (R j v)),
    let q := phiS t j ⟨z, b, s⟩
    let u := phiR q.1 v ⟨j, q.2.2, r⟩
    appendPath (psiB t u.1 ⟨q.1, q.2.1, u.2.1⟩) u.2.2 =
      FinitePath.cons b (psiB z v ⟨j, s, r⟩)

private abbrev Output {n k : ℕ} (A : CountMat n n)
    (R : CountMat n k) (S : CountMat k n) (d : ℕ) (i w : Fin n) :=
  Σ t : Fin k, Fin (R i t) ×
    (Σ v : Fin n, Fin (S t v) × FinitePath A d v w)

private def doubleSweep {n k d : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    {i j w : Fin n} {z : Fin k} (alpha : FinitePath A d i j)
    (r : Fin (R j z)) (s : Fin (S z w)) : Output A R S d i w :=
  let p := sweep phiR alpha r
  let q := sweep phiS p.2.2 s
  ⟨p.1, p.2.1, q.1, q.2.1, q.2.2⟩

/- The first equivalence keeps the RS middle vertex inside the psi fiber. -/
private def pairEquiv {n k m : ℕ} {A : CountMat n n}
    {R : CountMat n k} {S : CountMat k n}
    (psi : ∀ i v, EdgePair R S i v ≃ FinitePath A m i v)
    (d : ℕ) (i w : Fin n) : Output A R S d i w ≃ Split A m d i w where
  toFun x := ⟨x.2.2.1, psi i x.2.2.1 ⟨x.1, x.2.1, x.2.2.2.1⟩,
    x.2.2.2.2⟩
  invFun x :=
    let rs := (psi i x.1).symm x.2.1
    ⟨rs.1, rs.2.1, x.1, rs.2.2, x.2.2⟩
  left_inv := by
    rintro ⟨t, r, v, s, gamma⟩
    dsimp only
    rw [(psi i v).symm_apply_apply]
  right_inv := by
    rintro ⟨v, alpha, gamma⟩
    dsimp only
    have h := (psi i v).apply_symm_apply alpha
    simpa only [Sigma.eta, Prod.mk.eta] using
      congrArg (fun p : FinitePath A m i v =>
        (⟨v, p, gamma⟩ : Split A m d i w)) h

/- encode = concatenate after psi; decode = cut followed by the same psi⁻¹.
   Both inverse proofs are carried by the two constituent equivalences. -/
private def encodingEquiv {n k m : ℕ} {A : CountMat n n}
    {R : CountMat n k} {S : CountMat k n}
    (psi : ∀ i v, EdgePair R S i v ≃ FinitePath A m i v)
    (d : ℕ) (i w : Fin n) : Output A R S d i w ≃ FinitePath A (m + d) i w :=
  (pairEquiv psi d i w).trans (concatenateEquiv A m d i w)

/-- Whole numbered-word invariant; the lag of psi remains m in every branch. -/
private theorem whole_word_invariant {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k} {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w)
    (hAligned : AlignedA phiR phiS psiA) :
    ∀ {d : ℕ} {i j w : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)) (s : Fin (S z w)),
      let p := sweep phiR alpha r
      let q := sweep phiS p.2.2 s
      pathWord (psiA i q.1 ⟨p.1, p.2.1, q.2.1⟩) ++ pathWord q.2.2 =
        pathWord alpha ++ pathWord (psiA j w ⟨z, r, s⟩) := by
  intro d i j w z alpha
  induction alpha with
  | nil i =>
      intro r s
      simp only [sweep, pathWord, List.append_nil, List.nil_append]
      rfl
  | @cons d i j h a tail ih =>
      intro r s
      rcases hF : sweep phiR tail r with ⟨t, r₀, beta⟩
      rcases hG : sweep phiS beta s with ⟨v, s₀, gamma⟩
      rcases hR : phiR i t ⟨j, a, r₀⟩ with ⟨u, r₁, b⟩
      rcases hS : phiS u v ⟨t, b, s₀⟩ with ⟨q, s₁, a'⟩
      have hi := ih r s
      dsimp only at hi
      rw [hF, hG] at hi
      have ha := hAligned a r₀ s₀
      dsimp only at ha
      rw [hR, hS] at ha
      have haw := congrArg pathWord ha
      simp only [word_appendPath, pathWord] at haw
      -- Transport complete dependent outputs through fixed-codomain functions.
      -- Each congrArg keeps its Sigma index and all dependent fields together.
      have hFR : sweep phiR (FinitePath.cons a tail) r =
          (⟨u, r₁, FinitePath.cons b beta⟩ :
            Σ x : Fin k, Fin (R i x) × FinitePath B (d + 1) x z) := by
        exact (congrArg
          (fun rest : Σ x : Fin k, Fin (R j x) × FinitePath B d x z =>
            let square := phiR i rest.1 ⟨j, a, rest.2.1⟩
            (⟨square.1, square.2.1, FinitePath.cons square.2.2 rest.2.2⟩ :
              Σ x : Fin k, Fin (R i x) × FinitePath B (d + 1) x z)) hF).trans
          (congrArg
            (fun square : EdgePair R B i t =>
              (⟨square.1, square.2.1, FinitePath.cons square.2.2 beta⟩ :
                Σ x : Fin k, Fin (R i x) × FinitePath B (d + 1) x z)) hR)
      have hGS : sweep phiS (FinitePath.cons b beta) s =
          (⟨q, s₁, FinitePath.cons a' gamma⟩ :
            Σ x : Fin n, Fin (S u x) × FinitePath A (d + 1) x w) := by
        exact (congrArg
          (fun rest : Σ x : Fin n, Fin (S t x) × FinitePath A d x w =>
            let square := phiS u rest.1 ⟨t, b, rest.2.1⟩
            (⟨square.1, square.2.1, FinitePath.cons square.2.2 rest.2.2⟩ :
              Σ x : Fin n, Fin (S u x) × FinitePath A (d + 1) x w)) hG).trans
          (congrArg
            (fun square : EdgePair S A u v =>
              (⟨square.1, square.2.1, FinitePath.cons square.2.2 gamma⟩ :
                Σ x : Fin n, Fin (S u x) × FinitePath A (d + 1) x w)) hS)
      have hword :
          (let p := sweep phiR (FinitePath.cons a tail) r
           let q' := sweep phiS p.2.2 s
           pathWord (psiA i q'.1 ⟨p.1, p.2.1, q'.2.1⟩) ++ pathWord q'.2.2) =
            pathWord (psiA i q ⟨u, r₁, s₁⟩) ++
              ((⟨q, v, a'⟩ : Edge A) :: pathWord gamma) := by
        exact (congrArg
          (fun p : Σ x : Fin k, Fin (R i x) × FinitePath B (d + 1) x z =>
            let q' := sweep phiS p.2.2 s
            pathWord (psiA i q'.1 ⟨p.1, p.2.1, q'.2.1⟩) ++ pathWord q'.2.2)
          hFR).trans
          (congrArg
            (fun q' : Σ x : Fin n, Fin (S u x) × FinitePath A (d + 1) x w =>
              pathWord (psiA i q'.1 ⟨u, r₁, q'.2.1⟩) ++ pathWord q'.2.2) hGS)
      refine hword.trans ?_
      calc
        pathWord (psiA i q ⟨u, r₁, s₁⟩) ++
            (⟨q, v, a'⟩ :: pathWord gamma) =
            (pathWord (psiA i q ⟨u, r₁, s₁⟩) ++ [⟨q, v, a'⟩]) ++
              pathWord gamma := by
                simp only [List.append_assoc, List.cons_append, List.nil_append]
        _ = (⟨i, j, a⟩ :: pathWord (psiA j v ⟨t, r₀, s₀⟩)) ++
              pathWord gamma := congrArg (fun l => l ++ pathWord gamma) haw
        _ = ⟨i, j, a⟩ :: (pathWord tail ++ pathWord (psiA h w ⟨z, r, s⟩)) := by
              simpa only [List.cons_append] using
                congrArg (List.cons (⟨i, j, a⟩ : Edge A)) hi

/- Equation (1), with the full concatenate/length-transport/cut composite.
   The decoder receives a path of length m+d and cuts after m, never d. -/
private theorem composition_fixed_lag {n k m d : ℕ}
    {A : CountMat n n} {B : CountMat k k} {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w)
    (hAligned : AlignedA phiR phiS psiA)
    {i j w : Fin n} {z : Fin k} (alpha : FinitePath A d i j)
    (r : Fin (R j z)) (s : Fin (S z w)) :
    doubleSweep phiR phiS alpha r s =
      (encodingEquiv psiA d i w).symm
        (lengthCast (Nat.add_comm d m) (concatenate alpha (psiA j w ⟨z, r, s⟩))) := by
  apply (encodingEquiv psiA d i w).injective
  rw [(encodingEquiv psiA d i w).apply_symm_apply]
  suffices hw :
      pathWord ((encodingEquiv psiA d i w) (doubleSweep phiR phiS alpha r s)) =
        pathWord (lengthCast (Nat.add_comm d m)
          (concatenate alpha (psiA j w ⟨z, r, s⟩))) from
    sigma_mk_injective (word_endpoint_injective _ _ hw)
  change pathWord
    (concatenate
      (psiA i (doubleSweep phiR phiS alpha r s).2.2.1
        ⟨(doubleSweep phiR phiS alpha r s).1,
          (doubleSweep phiR phiS alpha r s).2.1,
          (doubleSweep phiR phiS alpha r s).2.2.2.1⟩)
      (doubleSweep phiR phiS alpha r s).2.2.2.2) = _
  rw [word_concatenate, word_lengthCast, word_concatenate]
  exact whole_word_invariant phiR phiS psiA hAligned alpha r s

/-- Both sides below are the original dependent output tuple, in sweep order. -/
def BalancedA {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w) : Prop :=
  ∀ {i j w : Fin n} {z : Fin k}
    (alpha : FinitePath A m i j) (r : Fin (R j z)) (s : Fin (S z w)),
    let p := sweep phiR alpha r
    let q := sweep phiS p.2.2 s
    (⟨p.1, p.2.1, q.1, q.2.1, q.2.2⟩ :
      Σ u : Fin k, Fin (R i u) ×
        (Σ v : Fin n, Fin (S u v) × FinitePath A m v w)) =
      (let rs := (psiA i j).symm alpha
       ⟨rs.1, rs.2.1, j, rs.2.2, psiA j w ⟨z, r, s⟩⟩)

def BalancedB {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiB : ∀ t v, EdgePair S R t v ≃ FinitePath B m t v) : Prop :=
  ∀ {t z v : Fin k} {j : Fin n}
    (beta : FinitePath B m t z) (s : Fin (S z j)) (r : Fin (R j v)),
    let p := sweep phiS beta s
    let q := sweep phiR p.2.2 r
    (⟨p.1, p.2.1, q.1, q.2.1, q.2.2⟩ :
      Σ u : Fin n, Fin (S t u) ×
        (Σ x : Fin k, Fin (R u x) × FinitePath B m x v)) =
      (let sr := (psiB t z).symm beta
       ⟨sr.1, sr.2.1, z, sr.2.2, psiB z v ⟨j, s, r⟩⟩)

private theorem balanced_of_aligned {n k m : ℕ}
    {A : CountMat n n} {B : CountMat k k} {R : CountMat n k} {S : CountMat k n}
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w)
    (hAligned : AlignedA phiR phiS psiA) : BalancedA phiR phiS psiA := by
  intro i j w z alpha r s
  change doubleSweep phiR phiS alpha r s = _
  rw [composition_fixed_lag phiR phiS psiA hAligned alpha r s]
  have hself : ∀ p : FinitePath A (m + m) i w,
      lengthCast (Nat.add_comm m m) p = p := by
    intro p
    rfl
  rw [hself]
  change (pairEquiv psiA m i w).symm
      ((concatenateEquiv A m m i w).symm
        ((concatenateEquiv A m m i w) ⟨j, alpha, psiA j w ⟨z, r, s⟩⟩)) = _
  rw [(concatenateEquiv A m m i w).symm_apply_apply]
  rfl

/-- BDR Proposition 3.4 on the same essential matrices, fixed positive lag,
    arbitrary original R,S, and all four original path isomorphisms.
    Essentiality and positivity are retained, though the implication is stronger.
    This theorem's source is proposed; no compiled status is asserted here. -/
theorem originalBDRProposition3_4 {n k m : ℕ}
    (A : CountMat n n) (B : CountMat k k) (R : CountMat n k) (S : CountMat k n)
    (_essentialA :
      (∀ i : Fin n, ∃ j : Fin n, A i j ≠ 0) ∧
      (∀ j : Fin n, ∃ i : Fin n, A i j ≠ 0))
    (_essentialB :
      (∀ t : Fin k, ∃ z : Fin k, B t z ≠ 0) ∧
      (∀ z : Fin k, ∃ t : Fin k, B t z ≠ 0))
    (_positiveLag : 0 < m)
    (phiR : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z)
    (phiS : ∀ t w, EdgePair B S t w ≃ EdgePair S A t w)
    (psiA : ∀ i w, EdgePair R S i w ≃ FinitePath A m i w)
    (psiB : ∀ t v, EdgePair S R t v ≃ FinitePath B m t v)
    (hA : AlignedA phiR phiS psiA) (hB : AlignedB phiR phiS psiB) :
    BalancedA phiR phiS psiA ∧ BalancedB phiR phiS psiB := by
  constructor
  · exact balanced_of_aligned phiR phiS psiA hA
  · exact balanced_of_aligned (A := B) (B := A) (R := S) (S := R)
      phiS phiR psiB hB

set_option pp.universes true in
set_option pp.explicit true in
set_option pp.fullNames true in
#check @originalBDRProposition3_4
#print axioms originalBDRProposition3_4
#print axioms whole_word_invariant


/- Scoped kernel-object evidence; no proof pretty-print or raw Expr export. -/
run_cmd do
  let env ← Lean.getEnv
  for name in [``lengthCast, ``word_lengthCast, ``Split, ``identityLift, ``concatenate, ``word_concatenate, ``word_endpoint_injective, ``split_word_injective, ``cut, ``word_cut, ``concatenateEquiv, ``word_appendPath, ``AlignedA, ``AlignedB, ``Output, ``doubleSweep, ``pairEquiv, ``encodingEquiv, ``whole_word_invariant, ``composition_fixed_lag, ``BalancedA, ``BalancedB, ``balanced_of_aligned, ``originalBDRProposition3_4] do
    let some ci := env.checked.get.find? name
      | throwError "checked kernel object missing: {name}"
    let some value := ci.value? (allowOpaque := true)
      | throwError "kernel value missing: {name}"
    if ci.type.hasFVar || ci.type.hasMVar || ci.type.hasLooseBVars ||
        value.hasFVar || value.hasMVar || value.hasLooseBVars then
      throwError "non-closed object: {name}"
    let axioms ← Lean.collectAxioms name
    if axioms.contains ``sorryAx then
      throwError "admitted object: {name}"
    Lean.logInfo m!"KERNEL_OBJECT {name} theorem={ci.isTheorem} closed_type=true closed_value=true axioms={axioms} direct_constants={value.getUsedConstants}"
  let axioms ← Lean.collectAxioms ``originalBDRProposition3_4
  unless axioms.size == 3 && axioms.contains ``propext &&
      axioms.contains ``Classical.choice && axioms.contains ``Quot.sound do
    throwError "final theorem axiom closure is not exactly the standard three: {axioms}"
  Lean.logInfo "EXACT_STANDARD_THREE_CONFIRMED"

#print AlignedA
#print AlignedB
#print BalancedA
#print BalancedB

end D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced

/- Full 6.2 canonical numbered-window relations; source proposal, unverified here. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

namespace D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport

def reverseEdge {n : ℕ} {A : CountMat n n} (a : Edge A) : Edge A.transpose :=
  ⟨a.target, a.source, a.number⟩

def reversePath {n : ℕ} {A : CountMat n n} (x : Path A) : Path A.transpose :=
  ⟨fun i => reverseEdge (x.val (-i-1)), fun i => by
    change (x.val (-i-1)).source = (x.val (-(i+1)-1)).target
    have h := x.property (-(i+1)-1)
    simpa only [show -(i+1)-1+1 = -i-1 by omega] using h.symm⟩

def window {p : ℕ} {M : CountMat p p} (x : Path M) :
    (d : ℕ) → (i : ℤ) → Σ j, FinitePath M d (x.val i).source j
  | 0, i => ⟨(x.val i).source, .nil _⟩
  | d+1, i =>
    let tail := window x d (i+1)
    ⟨tail.1, .cons ((x.property i) ▸ (x.val i).number) tail.2⟩

theorem window_endpoint {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    (window x d i).1 = (x.val (i+d)).source := by
  induction d generalizing i with
  | zero => simp only [window, Int.natCast_zero, add_zero]
  | succ d ih =>
    change (window x d (i+1)).1 = _
    rw [ih]
    rw [show i+1+(d:ℤ) = i+(↑(d+1):ℤ) by push_cast; omega]

theorem history_trace {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (x : Path M) (r : ℤ → Q)
    (proj : ∀ i, L.project (r i) = (x.val i).source)
    (step : ∀ i (h : L.project (r (i+1)) = (x.val i).target),
      (L.lift (x.val i) ⟨r (i+1),h⟩).val = r i) :
    ∀ d i (q : {q : Q // L.project q = (window x d i).1}),
      q.val = r (i+d) → (L.liftPath (window x d i).2 q).val = r i := by
  have liftcast (a : Edge M) (v : Fin p) (h : a.target = v)
      (q : {q : Q // L.project q = v}) :
      (L.lift ⟨a.source,v,h ▸ a.number⟩ q).val =
      (L.lift a ⟨q.val,q.property.trans h.symm⟩).val := by cases h; rfl
  intro d
  induction d with
  | zero => intro i q h; simpa only [window, IncomingLift.liftPath, Int.natCast_zero, add_zero] using h
  | succ d ih =>
    intro i q h
    have hq : q.val = r (i+1+d) :=
      h.trans (congrArg r (by push_cast; omega))
    have ht := ih (i+1) q hq
    change (L.lift ⟨(x.val i).source,(x.val (i+1)).source,
      (x.property i) ▸ (x.val i).number⟩
      (L.liftPath (window x d (i+1)).2 q)).val = r i
    rw [liftcast]
    have hr : L.liftPath (window x d (i+1)).2 q = ⟨r (i+1),proj (i+1)⟩ :=
      Subtype.ext ht
    rw [hr]
    exact step i _

theorem cast_edge {p : ℕ} {M : CountMat p p} (a : Edge M) (v : Fin p)
    (h : a.target = v) :
    (⟨a.source,v,h ▸ a.number⟩ : Edge M) = a := by cases h; rfl

theorem window_word {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    pathWord (window x d i).2 = List.ofFn (fun j : Fin d => x.val (i+j.val)) := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    change _ :: pathWord (window x d (i+1)).2 = _
    rw [cast_edge (x.val i) _ (x.property i), ih, List.ofFn_succ]
    simp only [Fin.val_zero, Int.natCast_zero, add_zero]
    apply congrArg (List.cons (x.val i))
    apply congrArg List.ofFn
    funext j
    apply congrArg x.val
    change i + 1 + (j.val : ℤ) = i + ((j.val + 1 : ℕ) : ℤ)
    push_cast
    omega

theorem reverse_word {p : ℕ} {M : CountMat p p} {d : ℕ} {i j : Fin p}
    (alpha : FinitePath M d i j) :
    pathWord (reverseFinitePath alpha) = (pathWord alpha).reverse.map reverseEdge := by
  induction alpha with
  | nil => rfl
  | @cons d u v z edge tail ih =>
    calc
      pathWord (reverseFinitePath (.cons edge tail)) =
          pathWord (reverseFinitePath tail) ++ [(⟨v,u,edge⟩ : Edge M.transpose)] :=
        _root_.D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.word_appendPath (A := M.transpose) (reverseFinitePath tail) edge
      _ = (pathWord tail).reverse.map (@reverseEdge p M) ++ [⟨v,u,edge⟩] :=
        congrArg (fun w : List (Edge M.transpose) => w ++ [⟨v,u,edge⟩]) ih
      _ = (pathWord (.cons edge tail)).reverse.map (@reverseEdge p M) := by
        simp only [pathWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,reverseEdge]

theorem past_word {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    pathWord (reverseFinitePath (window (reversePath x) d (-i)).2) =
      (List.ofFn (fun j : Fin d => x.val (i-(j.val:ℤ)-1))).reverse := by
  rw [reverse_word,window_word,List.map_reverse,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  change reverseEdge (reverseEdge (x.val (-(-i+(j.val:ℤ))-1))) = _
  rw [show -(-i+(j.val:ℤ))-1 = i-(j.val:ℤ)-1 by omega]
  rfl

end D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport
