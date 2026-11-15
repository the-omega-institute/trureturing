/- GID: D5/S3/Quantum/Routing/HannUniformSection
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannUniformSection
   mirror-E: none(waiver:noncomputational)
   anchors: [muellerregensburger2016elementary]
   utility: none
   digest: Binary original-leaf certificates for signed loaded-record probability sections. -/

import D5.S3.Quantum.Routing.HannExactForest
import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import Mathlib.Analysis.Convex.Hull

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Routing.HannUniformSection

open ReversibleQram (Address)
open HannRouterProfiles (Router)
open HannSpatialQram (Qutrit)
open HannSignedCertificate HannExactForest

/-- The real probability section of the original loaded records. -/
def Section (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) : Set ℝ :=
  {z | ∃ p : Address n → ℝ, (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
    synthesis n q bus (fun a => (p a : ℂ)) = (z : ℂ) • vacuumRecord n q}

/-- Real scalars in the literal node equations; neither rows nor coordinates change. -/
def RealLocal (t z l r : ℝ) : Prop :=
  if t = 1 then z = l + r
  else if t = -(1 / 2 : ℝ) then l = -z ∧ r = -z
  else z = 0 ∧ l = 0 ∧ r = 0

def RealEquations : (n : ℕ) → (Router n → ℝ) → (Address n → ℝ) → (Node n → ℝ) → Prop
  | 0, _, x, c => c () = x ()
  | n + 1, q, x, c =>
    RealLocal (q none) (c none) (c (some (false, root n))) (c (some (true, root n))) ∧
    ∀ b, RealEquations n (restrict n q b) (fun a => x (b, a)) (fun v => c (some (b, v)))

private theorem real_equations_cast (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) :
    RealEquations n q x c ↔ Equations n q (fun a => (x a : ℂ)) (fun v => (c v : ℂ)) := by
  induction n with
  | zero => simp [RealEquations, Equations, sub_eq_zero]
  | succ n ih =>
    simp only [RealEquations, Equations, childValues, childCoeff, ← ih]
    apply and_congr_left
    intro _
    unfold RealLocal Local
    split_ifs <;> push_cast <;> constructor <;> intro h
    · exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (by exact_mod_cast h))
    · exact_mod_cast (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h))
    · rcases h with ⟨hl, hr⟩; constructor <;> push_cast <;> simp_all
    · rcases h with ⟨hl, hr⟩; constructor <;> exact_mod_cast (eq_neg_iff_add_eq_zero.mpr (by assumption))
    · simpa using h
    · simpa using h

private theorem real_equations_zero (n : ℕ) (q : Router n → ℝ) :
    RealEquations n q (fun _ => 0) (fun _ => 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ⟨?_, fun b => ih _⟩
    simp [RealLocal]

private theorem nodes_zero_of_leaves_zero (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) (he : RealEquations n q x c)
    (hx : x = 0) : c = 0 := by
  induction n with
  | zero => ext v; cases v; simpa [RealEquations, hx] using he
  | succ n ih =>
    obtain ⟨hl, hs⟩ := he
    have hc (b : Bool) : (fun v => c (some (b, v))) = 0 :=
      ih _ _ _ (hs b) (by simp [hx])
    have hroot : c none = 0 := by
      have h0 := congrFun (hc false) (root n)
      have h1 := congrFun (hc true) (root n)
      unfold RealLocal at hl
      split_ifs at hl <;> simp_all
    ext v
    cases v with
    | none => exact hroot
    | some v => exact congrFun (hc v.1) v.2

private def sgn (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

private theorem sgn_zero : sgn 0 = 0 := by norm_num [sgn]

private theorem sgn_neg (t : ℝ) : sgn (-t) = -sgn t := by
  unfold sgn
  split_ifs <;> linarith

private theorem sgn_ne_zero {t : ℝ} (h : t ≠ 0) : sgn t ≠ 0 := by
  unfold sgn
  split_ifs <;> simp_all <;> linarith

private structure Piece (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) where
  leaf : Address n → ℝ
  node : Node n → ℝ
  equations : RealEquations n q leaf node
  binary : ∀ a, leaf a = 0 ∨ leaf a = 1
  leaf_support : ∀ a, leaf a ≠ 0 → 0 < x a
  conformal : ∀ v, node v = 0 ∨ node v = sgn (c v)

private def zeroPiece (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) : Piece n q x c where
  leaf := 0
  node := 0
  equations := real_equations_zero n q
  binary := fun _ => Or.inl rfl
  leaf_support := by simp
  conformal := fun _ => Or.inl rfl

private def joinPiece (n : ℕ) (q : Router (n + 1) → ℝ)
    (x : Address (n + 1) → ℝ) (c : Node (n + 1) → ℝ)
    (L : Piece n (restrict n q false) (fun a => x (false, a)) (fun v => c (some (false, v))))
    (R : Piece n (restrict n q true) (fun a => x (true, a)) (fun v => c (some (true, v))))
    (t : ℝ) (ht : t = 0 ∨ t = sgn (c none))
    (he : RealLocal (q none) t (L.node (root n)) (R.node (root n))) :
    Piece (n + 1) q x c where
  leaf a := if a.1 then R.leaf a.2 else L.leaf a.2
  node v := match v with
    | none => t
    | some (false, v) => L.node v
    | some (true, v) => R.node v
  equations := ⟨he, by intro b; cases b; exact L.equations; exact R.equations⟩
  binary := by rintro ⟨b, a⟩; cases b; exact L.binary a; exact R.binary a
  leaf_support := by rintro ⟨b, a⟩; cases b; exact L.leaf_support a; exact R.leaf_support a
  conformal := by
    intro v
    cases v with
    | none => exact ht
    | some v => cases v with | mk b v => cases b; exact L.conformal v; exact R.conformal v

private theorem join_nonzero_left (n : ℕ) (q : Router (n + 1) → ℝ)
    (x : Address (n + 1) → ℝ) (c : Node (n + 1) → ℝ)
    (L : Piece n (restrict n q false) (fun a => x (false, a)) (fun v => c (some (false, v))))
    (R : Piece n (restrict n q true) (fun a => x (true, a)) (fun v => c (some (true, v))))
    (t : ℝ) (ht : t = 0 ∨ t = sgn (c none))
    (he : RealLocal (q none) t (L.node (root n)) (R.node (root n)))
    (hL : L.leaf ≠ 0) : (joinPiece n q x c L R t ht he).leaf ≠ 0 := by
  intro h
  apply hL
  ext a
  exact congrFun h (false, a)

private theorem join_nonzero_right (n : ℕ) (q : Router (n + 1) → ℝ)
    (x : Address (n + 1) → ℝ) (c : Node (n + 1) → ℝ)
    (L : Piece n (restrict n q false) (fun a => x (false, a)) (fun v => c (some (false, v))))
    (R : Piece n (restrict n q true) (fun a => x (true, a)) (fun v => c (some (true, v))))
    (t : ℝ) (ht : t = 0 ∨ t = sgn (c none))
    (he : RealLocal (q none) t (L.node (root n)) (R.node (root n)))
    (hR : R.leaf ≠ 0) : (joinPiece n q x c L R t ht he).leaf ≠ 0 := by
  intro h
  apply hR
  ext a
  exact congrFun h (true, a)

end D5.S3.Quantum.Routing.HannUniformSection
