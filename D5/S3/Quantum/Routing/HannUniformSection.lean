/- GID: D5/S3/Quantum/Routing/HannUniformSection
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannUniformSection
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Binary original-leaf certificates for signed loaded-record probability sections. -/

import D5.S3.Quantum.Routing.HannExactForest
import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Finite.Lemmas

/-! Real node rounding and the probability section of the original signed records. -/

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
    change (RealLocal _ _ _ _ ∧ _) ↔ (Local _ _ _ _ ∧ _)
    apply and_congr
    swap
    · exact forall_congr' (fun b => ih _ _ _)
    simp only [childValues]
    by_cases hu : q none = 1
    · simp only [RealLocal, Local, ite_eq_left hu]
      constructor
      · intro h
        have hc : (c none : ℂ) = (c (some (false, root n)) : ℂ) + (c (some (true, root n)) : ℂ) := by exact_mod_cast h
        linear_combination hc
      · intro h
        have hc : (c none : ℂ) = (c (some (false, root n)) : ℂ) + (c (some (true, root n)) : ℂ) := by linear_combination h
        exact_mod_cast hc
    · by_cases hd : q none = -(1 / 2 : ℝ)
      · simp only [RealLocal, Local, ite_eq_right hu, ite_eq_left hd]
        constructor
        · rintro ⟨hl, hr⟩
          constructor <;> simp [hl, hr]
        · rintro ⟨hl, hr⟩
          constructor
          · exact_mod_cast (eq_neg_iff_add_eq_zero.mpr hl)
          · exact_mod_cast (eq_neg_iff_add_eq_zero.mpr hr)
      · simp only [RealLocal, Local, ite_eq_right hu, ite_eq_right hd]
        norm_cast

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
      ih _ _ _ (hs b) (by ext a; simp [hx])
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
  split_ifs <;> norm_num
  exact h (by linarith)

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

private theorem piece_nonzero_of_root (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) (P : Piece n q x c)
    (h : P.node (root n) ≠ 0) : P.leaf ≠ 0 := by
  intro hz
  exact h (congrFun (nodes_zero_of_leaves_zero n q P.leaf P.node P.equations hz) (root n))

private theorem rounding (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) (hx : ∀ a, 0 ≤ x a)
    (he : RealEquations n q x c) :
    ∃ P : Piece n q x c, P.node (root n) = sgn (c (root n)) ∧ (x ≠ 0 → P.leaf ≠ 0) := by
  induction n with
  | zero =>
    have hc : c () = x () := he
    by_cases hz : x () = 0
    · refine ⟨zeroPiece 0 q x c, ?_, ?_⟩
      · simp [zeroPiece, root, hc, hz, sgn_zero]
      · intro h; exact (h (funext (fun a => by cases a; exact hz))).elim
    · have hp : 0 < x () := lt_of_le_of_ne (hx ()) (Ne.symm hz)
      refine ⟨⟨fun _ => 1, fun _ => 1, rfl, fun _ => Or.inr rfl,
        fun a _ => by cases a; exact hp, ?_⟩, ?_, ?_⟩
      · intro v; cases v; right; simp [hc, sgn, hp]
      · simp [root, hc, sgn, hp]
      · intro _ h; exact one_ne_zero (congrFun h ())
  | succ n ih =>
    obtain ⟨hloc, hsub⟩ := he
    obtain ⟨L, hL, hLn⟩ := ih (restrict n q false) (fun a => x (false, a))
      (fun v => c (some (false, v))) (fun a => hx (false, a)) (hsub false)
    obtain ⟨R, hR, hRn⟩ := ih (restrict n q true) (fun a => x (true, a))
      (fun v => c (some (true, v))) (fun a => hx (true, a)) (hsub true)
    let ZL := zeroPiece n (restrict n q false) (fun a => x (false, a)) (fun v => c (some (false, v)))
    let ZR := zeroPiece n (restrict n q true) (fun a => x (true, a)) (fun v => c (some (true, v)))
    have both_nonzero (t : ℝ) (ht : t = 0 ∨ t = sgn (c none))
        (hh : RealLocal (q none) t (L.node (root n)) (R.node (root n)))
        (hn : x ≠ 0) : (joinPiece n q x c L R t ht hh).leaf ≠ 0 := by
      by_cases hxl : (fun a => x (false, a)) = 0
      · apply join_nonzero_right n q x c L R t ht hh
        apply hRn
        intro hxr
        apply hn
        ext a
        obtain ⟨b, a⟩ := a
        cases b
        · exact congrFun hxl a
        · exact congrFun hxr a
      · exact join_nonzero_left n q x c L R t ht hh (hLn hxl)
    by_cases hu : q none = 1
    · have hsum : c none = c (some (false, root n)) + c (some (true, root n)) := by
        simpa [RealLocal, hu] using hloc
      by_cases hz : c none = 0
      · have hr : c (some (true, root n)) = -c (some (false, root n)) := by linarith
        have hh : RealLocal (q none) 0 (L.node (root n)) (R.node (root n)) := by
          simp [RealLocal, hu, hL, hR, hr, sgn_neg]
        refine ⟨joinPiece n q x c L R 0 (Or.inl rfl) hh, ?_, ?_⟩
        · simp [joinPiece, root, hz, sgn_zero]
        · exact both_nonzero 0 (Or.inl rfl) hh
      · have finish_left (hs : sgn (c (some (false, root n))) = sgn (c none)) :
            ∃ P : Piece (n + 1) q x c,
              P.node (root (n + 1)) = sgn (c (root (n + 1))) ∧ (x ≠ 0 → P.leaf ≠ 0) := by
          have hh : RealLocal (q none) (sgn (c none)) (L.node (root n)) (ZR.node (root n)) := by
            simp [RealLocal, hu, hL, hs, ZR, zeroPiece]
          let P := joinPiece n q x c L ZR (sgn (c none)) (Or.inr rfl) hh
          refine ⟨P, rfl, fun _ => piece_nonzero_of_root (n + 1) q x c P ?_⟩
          exact sgn_ne_zero hz
        have finish_right (hs : sgn (c (some (true, root n))) = sgn (c none)) :
            ∃ P : Piece (n + 1) q x c,
              P.node (root (n + 1)) = sgn (c (root (n + 1))) ∧ (x ≠ 0 → P.leaf ≠ 0) := by
          have hh : RealLocal (q none) (sgn (c none)) (ZL.node (root n)) (R.node (root n)) := by
            simp [RealLocal, hu, hR, hs, ZL, zeroPiece]
          let P := joinPiece n q x c ZL R (sgn (c none)) (Or.inr rfl) hh
          refine ⟨P, rfl, fun _ => piece_nonzero_of_root (n + 1) q x c P ?_⟩
          exact sgn_ne_zero hz
        by_cases hp : 0 < c none
        · by_cases hl : 0 < c (some (false, root n))
          · exact finish_left (by simp [sgn, hl, hp])
          · have hr : 0 < c (some (true, root n)) := by linarith
            exact finish_right (by simp [sgn, hr, hp])
        · have hm : c none < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
          by_cases hl : c (some (false, root n)) < 0
          · exact finish_left (by simp [sgn, hl, hm, hp, not_lt_of_ge hl.le])
          · have hr : c (some (true, root n)) < 0 := by linarith
            exact finish_right (by simp [sgn, hr, hm, hp, not_lt_of_ge hr.le])
    · by_cases hd : q none = -(1 / 2 : ℝ)
      · have hlow : c (some (false, root n)) = -c none ∧
            c (some (true, root n)) = -c none := by simpa only [RealLocal, ite_eq_right hu, ite_eq_left hd] using hloc
        have hh : RealLocal (q none) (sgn (c none)) (L.node (root n)) (R.node (root n)) := by
          simp only [RealLocal, ite_eq_right hu, ite_eq_left hd, hL, hR, hlow.1, hlow.2, sgn_neg]; trivial
        exact ⟨joinPiece n q x c L R (sgn (c none)) (Or.inr rfl) hh, rfl,
          both_nonzero _ (Or.inr rfl) hh⟩
      · have hz : c none = 0 ∧ c (some (false, root n)) = 0 ∧
            c (some (true, root n)) = 0 := by simpa only [RealLocal, ite_eq_right hu, ite_eq_right hd] using hloc
        have hh : RealLocal (q none) 0 (L.node (root n)) (R.node (root n)) := by
          simp only [RealLocal, ite_eq_right hu, ite_eq_right hd, hL, hR, hz.2.1, hz.2.2, sgn_zero]; trivial
        refine ⟨joinPiece n q x c L R 0 (Or.inl rfl) hh, ?_, both_nonzero _ (Or.inl rfl) hh⟩
        simp [joinPiece, root, hz.1, sgn_zero]

private theorem real_kernel_iff (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) :
    (matrix n q).mulVec (Sum.elim x c) = 0 ↔ RealEquations n q x c := by
  have hc : (complexMatrix n q).mulVec (coordinates n (fun a => (x a : ℂ)) (fun v => (c v : ℂ))) =
      fun i => ((matrix n q).mulVec (Sum.elim x c) i : ℂ) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, complexMatrix, coordinates, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v _
    cases v <;> simp [Complex.ofReal_mul]
  rw [real_equations_cast, ← kernel_iff_equations, hc]
  constructor
  · intro h; ext i; simp [h]
  · intro h; ext i; exact Complex.ofReal_injective (by simpa using congrFun h i)

private theorem real_lift (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1)
    (x : Address n → ℝ) (z : ℝ)
    (hx : synthesis n q bus (fun a => (x a : ℂ)) = (z : ℂ) • vacuumRecord n q) :
    ∃ c : Node n → ℝ, c (root n) = z ∧ RealEquations n q x c := by
  obtain ⟨c, hr, hk⟩ := (relation_iff_matrix_kernel n q bus hq _ _).mp hx
  refine ⟨fun v => (c v).re, by simpa using congrArg Complex.re hr, ?_⟩
  apply (real_kernel_iff n q x _).mp
  ext i
  have hi := congrArg Complex.re (congrFun hk i)
  simpa [Matrix.mulVec, dotProduct, complexMatrix, coordinates, Complex.mul_re,
    Sum.elim, Finset.sum_apply] using hi

private theorem real_relation (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1)
    (x : Address n → ℝ) (c : Node n → ℝ) (he : RealEquations n q x c) :
    synthesis n q bus (fun a => (x a : ℂ)) = (c (root n) : ℂ) • vacuumRecord n q := by
  apply (relation_iff_matrix_kernel n q bus hq _ _).mpr
  exact ⟨fun v => (c v : ℂ), rfl, (kernel_iff_equations n q _ _).mpr
    ((real_equations_cast n q x c).mp he)⟩

/-- A real kernel vector with nonnegative nonzero original leaves has a binary-leaf
certificate in the same kernel, supported and signed within the original vector. -/
theorem binary_conformal_kernel (n : ℕ) (q : Router n → ℝ)
    (x : Address n → ℝ) (c : Node n → ℝ) (hx : ∀ a, 0 ≤ x a) (hxn : x ≠ 0)
    (hk : (matrix n q).mulVec (Sum.elim x c) = 0) :
    ∃ (u : Address n → ℝ) (d : Node n → ℝ),
      (matrix n q).mulVec (Sum.elim u d) = 0 ∧ u ≠ 0 ∧
      (∀ a, u a = 0 ∨ u a = 1) ∧ (∀ a, u a ≠ 0 → 0 < x a) ∧
      (∀ v, d v = 0 ∨ d v = -1 ∨ d v = 1) ∧
      (∀ v, d v ≠ 0 → SignType.sign (d v) = SignType.sign (c v)) ∧
      SignType.sign (d (root n)) = SignType.sign (c (root n)) := by
  obtain ⟨P, hr, hn⟩ := rounding n q x c hx ((real_kernel_iff n q x c).mp hk)
  have sign_sgn (t : ℝ) : SignType.sign (sgn t) = SignType.sign t := by
    unfold sgn
    split_ifs with hp hm
    · simp [sign_pos hp]
    · simp [sign_neg hm]
    · have hz : t = 0 := by linarith
      simp [hz]
  refine ⟨P.leaf, P.node, (real_kernel_iff n q _ _).mpr P.equations, hn hxn,
    P.binary, P.leaf_support, ?_, ?_, ?_⟩
  · intro v
    rcases P.conformal v with hv | hv
    · exact Or.inl hv
    · rw [hv]; unfold sgn; split_ifs <;> simp
  · intro v hv
    rcases P.conformal v with hz | hs
    · exact (hv hz).elim
    · rw [hs]; exact sign_sgn _
  · rw [hr]; exact sign_sgn _

/-- Zero in the original probability section has a nonempty original-leaf zero sum,
even when zero is an interior point. The leaves lie in the given positive support. -/
theorem zero_certificate (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1)
    (p : Address n → ℝ) (hp : ∀ a, 0 ≤ p a) (hm : (∑ a, p a) = 1)
    (hz : synthesis n q bus (fun a => (p a : ℂ)) = 0) :
    ∃ S : Finset (Address n), S.Nonempty ∧ (∀ a ∈ S, 0 < p a) ∧
      (∑ a ∈ S, record n q bus a) = 0 := by
  classical
  obtain ⟨c, hr, he⟩ := real_lift n q bus hq p 0 (by simpa using hz)
  have hpn : p ≠ 0 := by intro h; simp [h] at hm
  obtain ⟨u, d, hk, hu, hb, hs, _, hsign, hroot⟩ :=
    binary_conformal_kernel n q p c hp hpn ((real_kernel_iff n q p c).mpr he)
  have hd : d (root n) = 0 := sign_eq_zero_iff.mp (by simpa [hr] using hroot)
  let S := Finset.univ.filter (fun a => u a = 1)
  have hi (a : Address n) : u a = if a ∈ S then 1 else 0 := by
    rcases hb a with h | h <;> simp [S, h]
  have hn : S.Nonempty := by
    by_contra h
    apply hu
    ext a
    rw [hi]
    simp [Finset.not_nonempty_iff_eq_empty.mp h]
  refine ⟨S, hn, ?_, ?_⟩
  · intro a ha
    exact hs a (by rw [hi]; simp [ha])
  · have hrel := real_relation n q bus hq u d ((real_kernel_iff n q u d).mp hk)
    rw [hd, Complex.ofReal_zero, zero_smul] at hrel
    convert hrel using 1
    ext e
    simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, hi,
      apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
    simp [← Finset.sum_filter]

private theorem circuit_binary (n : ℕ) (q : Router n → ℝ) (y : Variable n → ℝ)
    (hy : (matrix n q).mulVec y = 0) (hyn : y ≠ 0)
    (hpos : ∀ a, 0 ≤ y (.inl a))
    (hmin : ∀ w : Variable n → ℝ, (matrix n q).mulVec w = 0 → w ≠ 0 →
      Function.support w ⊆ Function.support y → Function.support w = Function.support y) :
    ∃ (t : ℝ) (u : Address n → ℝ) (d : Node n → ℝ),
      0 < t ∧ u ≠ 0 ∧ (∀ a, u a = 0 ∨ u a = 1) ∧
      (∀ v, d v = 0 ∨ d v = -1 ∨ d v = 1) ∧
      (matrix n q).mulVec (Sum.elim u d) = 0 ∧ y = t • Sum.elim u d := by
  classical
  let x : Address n → ℝ := fun a => y (.inl a)
  let c : Node n → ℝ := fun v => y (.inr v)
  have hsplit : Sum.elim x c = y := by ext v; cases v <;> rfl
  have hx : x ≠ 0 := by
    intro h
    have hc := nodes_zero_of_leaves_zero n q x c
      ((real_kernel_iff n q x c).mp (by simpa [hsplit] using hy)) h
    apply hyn
    rw [← hsplit, h, hc]
    ext v; cases v <;> rfl
  obtain ⟨u, d, hk, hu, hb, hs, ht, hsign, _⟩ :=
    binary_conformal_kernel n q x c hpos hx (by simpa [hsplit] using hy)
  let k : Variable n → ℝ := Sum.elim u d
  have hkn : k ≠ 0 := by intro h; apply hu; ext a; exact congrFun h (.inl a)
  have hsub : Function.support k ⊆ Function.support y := by
    intro v hv
    change k v ≠ 0 at hv
    change y v ≠ 0
    cases v with
    | inl a => exact (hs a hv).ne'
    | inr v =>
      intro hz
      have hsign0 := hsign v hv
      have hd := sign_eq_zero_iff.mp (by simpa [c, hz] using hsign0)
      exact hv hd
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
  have hua : u a = 1 := (hb a).resolve_left ha
  let t := x a
  have htp : 0 < t := hs a ha
  let w := y - t • k
  have hwK : (matrix n q).mulVec w = 0 := by
    simp [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hy, hk, k]
  have hwsub : Function.support w ⊆ Function.support y := by
    intro v hv
    change y v ≠ 0
    intro hz
    have hkz : k v = 0 := by
      by_contra h
      exact hsub h hz
    exact hv (by simp [w, hz, hkz])
  have hw : w = 0 := by
    by_contra hn
    have heq := hmin w hwK hn hwsub
    have haY : Sum.inl a ∈ Function.support y := htp.ne'
    have haW := heq.symm ▸ haY
    apply haW
    simp [w, k, hua, t, x]
  refine ⟨t, u, d, htp, hu, hb, ht, hk, ?_⟩
  exact sub_eq_zero.mp hw

private def indexedMatrix (n : ℕ) (q : Router n → ℝ) :
    Matrix (Fin (Fintype.card (Row n q))) (Variable n) ℝ :=
  fun i v => matrix n q ((Fintype.equivFin (Row n q)).symm i) v

private theorem indexed_kernel_iff (n : ℕ) (q : Router n → ℝ) (y : Variable n → ℝ) :
    (indexedMatrix n q).mulVec y = 0 ↔ (matrix n q).mulVec y = 0 := by
  constructor
  · intro h; ext i
    simpa [indexedMatrix, Matrix.mulVec, dotProduct] using
      congrFun h ((Fintype.equivFin (Row n q)) i)
  · intro h; ext i
    exact congrFun h ((Fintype.equivFin (Row n q)).symm i)

/-- Nonempty uniform original-leaf certificates, with their signed numerator. -/
def UniformCertificate (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (S : Finset (Address n)) (e : ℝ) : Prop :=
  S.Nonempty ∧ (e = -1 ∨ e = 0 ∨ e = 1) ∧
    (∑ a ∈ S, record n q bus a) = (e : ℂ) • vacuumRecord n q

private theorem binary_uniform (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1)
    (u : Address n → ℝ) (d : Node n → ℝ) (hu : u ≠ 0)
    (hb : ∀ a, u a = 0 ∨ u a = 1)
    (hd : ∀ v, d v = 0 ∨ d v = -1 ∨ d v = 1)
    (hk : (matrix n q).mulVec (Sum.elim u d) = 0) :
    ∃ S : Finset (Address n), UniformCertificate n q bus S (d (root n)) ∧
      (∀ a, u a = if a ∈ S then 1 else 0) ∧ (∑ a, u a) = S.card := by
  classical
  let S := Finset.univ.filter (fun a => u a = 1)
  have hi (a : Address n) : u a = if a ∈ S then 1 else 0 := by
    rcases hb a with h | h <;> simp [S, h]
  have hn : S.Nonempty := by
    by_contra h
    apply hu
    ext a
    rw [hi]
    simp [Finset.not_nonempty_iff_eq_empty.mp h]
  refine ⟨S, ⟨hn, ?_, ?_⟩, hi, ?_⟩
  · rcases hd (root n) with h | h | h <;> simp [h]
  · have hr := real_relation n q bus hq u d ((real_kernel_iff n q u d).mp hk)
    convert hr using 1
    ext e
    simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, hi,
      apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
    simp [← Finset.sum_filter]
  · simp [hi, ← Finset.sum_filter]

private def uniformValues (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) : Set ℝ :=
  {z | ∃ (S : Finset (Address n)) (e : ℝ), UniformCertificate n q bus S e ∧ z = e / S.card}

private theorem uniform_mem_section (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (S : Finset (Address n)) (e : ℝ) (h : UniformCertificate n q bus S e) :
    e / S.card ∈ Section n q bus := by
  classical
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast h.1.card_ne_zero
  let u : Address n → ℝ := fun a => if a ∈ S then 1 else 0
  have hs : (∑ a, u a) = S.card := by simp [u, ← Finset.sum_filter]
  have hr : synthesis n q bus (fun a => (u a : ℂ)) = (e : ℂ) • vacuumRecord n q := by
    convert h.2.2 using 1
    ext v
    simp [u, synthesis, apply_ite, ite_mul, ← Finset.sum_filter]
  refine ⟨fun a => (S.card : ℝ)⁻¹ * u a, ?_, ?_, ?_⟩
  · intro a; exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (by simp [u]; split_ifs <;> norm_num)
  · rw [← Finset.mul_sum, hs, inv_mul_cancel₀ hc]
  · have heq : (fun a => (((S.card : ℝ)⁻¹ * u a : ℝ) : ℂ)) =
        ((S.card : ℝ)⁻¹ : ℂ) • (fun a => (u a : ℂ)) := by ext a; simp
    rw [heq, map_smul, hr, smul_smul]
    congr 1
    push_cast
    ring

private theorem section_convex (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Convex ℝ (Section n q bus) := by
  rintro z ⟨p, hp, hpm, hpr⟩ w ⟨r, hr, hrm, hrr⟩ a b ha hb hab
  refine ⟨fun i => a * p i + b * r i, fun i => add_nonneg (mul_nonneg ha (hp i))
    (mul_nonneg hb (hr i)), ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hpm, hrm, mul_one]
    exact hab
  · have heq : (fun i => ((a * p i + b * r i : ℝ) : ℂ)) =
        (a : ℂ) • (fun i => (p i : ℂ)) + (b : ℂ) • (fun i => (r i : ℂ)) := by ext i; simp
    rw [heq, map_add, map_smul, map_smul, hpr, hrr, smul_smul, smul_smul, ← add_smul]
    congr 1
    simp [smul_eq_mul]

private theorem section_mem_hull (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1) (z : ℝ) (hz : z ∈ Section n q bus) :
    z ∈ convexHull ℝ (uniformValues n q bus) := by
  classical
  obtain ⟨p, hp, hm, hr⟩ := hz
  obtain ⟨d, hd, he⟩ := real_lift n q bus hq p z hr
  let y : Variable n → ℝ := Sum.elim p d
  have hy : (indexedMatrix n q).mulVec y = 0 :=
    (indexed_kernel_iff n q y).mpr ((real_kernel_iff n q p d).mpr he)
  obtain ⟨N, C, hsum, _, _, _, hC⟩ :=
    Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField.signConformalGlobalKernelCircuitDecomposition
      (indexedMatrix n q) y hy
  have hnonneg (j : Fin N) (a : Address n) : 0 ≤ C j (.inl a) := by
    rcases (hC j).2.2.1 (.inl a) with hj | hj
    · rw [hj]
    · by_contra hn
      have hneg : SignType.sign (C j (.inl a)) = -1 := sign_neg (lt_of_not_ge hn)
      have hpy : SignType.sign (p a) = -1 := by simpa [y, hneg] using hj.symm
      exact (not_lt_of_ge (hp a)) (sign_eq_neg_one_iff.mp hpy)
  have hcir (j : Fin N) := circuit_binary n q (C j)
    ((indexed_kernel_iff n q _).mp (hC j).2.1) (hC j).1 (hnonneg j)
    (fun w hw hn hs => (hC j).2.2.2 w ((indexed_kernel_iff n q w).mpr hw) hn hs)
  choose t u c ht hun hb hc hk hscale using hcir
  have hcert (j : Fin N) := binary_uniform n q bus hq (u j) (c j) (hun j) (hb j) (hc j) (hk j)
  choose S hS hi hmass using hcert
  let weight : Fin N → ℝ := fun j => t j * (S j).card
  let value : Fin N → ℝ := fun j => c j (root n) / (S j).card
  have hweight : (∑ j, weight j) = 1 := by
    calc
      (∑ j, weight j) = ∑ j, ∑ a, C j (.inl a) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [hscale j, Pi.smul_apply, smul_eq_mul, Sum.elim_inl,
          ← Finset.mul_sum, hmass, weight]
      _ = ∑ a, p a := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        simpa [y, Finset.sum_apply] using congrFun hsum (.inl a)
      _ = 1 := hm
  have hzsum : (∑ j, weight j • value j) = z := by
    calc
      (∑ j, weight j • value j) = ∑ j, C j (.inr (root n)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hcard : ((S j).card : ℝ) ≠ 0 := by exact_mod_cast (hS j).1.card_ne_zero
        simp only [weight, value, smul_eq_mul, hscale j, Pi.smul_apply, Sum.elim_inr]
        field_simp
      _ = d (root n) := by simpa [y, Finset.sum_apply] using congrFun hsum (.inr (root n))
      _ = z := hd
  exact mem_convexHull_of_exists_fintype weight value
    (fun j => mul_nonneg (ht j).le (Nat.cast_nonneg _)) hweight
    (fun j => ⟨S j, c j (root n), hS j, rfl⟩) hzsum

private theorem uniform_values_finite (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    (uniformValues n q bus).Finite := by
  let f : Finset (Address n) × Fin 3 → ℝ := fun se =>
    (if se.2 = 0 then -1 else if se.2 = 1 then 0 else 1) / se.1.card
  apply (Set.finite_range f).subset
  rintro z ⟨S, e, he, rfl⟩
  rcases he.2.1 with rfl | rfl | rfl
  · exact ⟨(S, 0), by simp [f]⟩
  · exact ⟨(S, 1), by simp [f]⟩
  · exact ⟨(S, 2), by simp [f]⟩

/-- The endpoint is attained by a uniform law on nonempty original leaves. -/
def UniformEndpoint (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) (z : ℝ) : Prop :=
  ∃ (S : Finset (Address n)) (e : ℝ), UniformCertificate n q bus S e ∧
    z = e / S.card ∧ 1 ≤ S.card ∧ S.card ≤ 2 ^ n

/-- The complete real probability section is empty or a closed interval whose
two endpoints have original-leaf uniform certificates. Zero has a nonempty zero
certificate whether it is an endpoint or an interior point. -/
theorem uniform_section (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1) :
    (Section n q bus = ∅ ∨ ∃ l r : ℝ, l ≤ r ∧ Section n q bus = Set.Icc l r ∧
      UniformEndpoint n q bus l ∧ UniformEndpoint n q bus r) ∧
    (0 ∈ Section n q bus → ∃ S : Finset (Address n), S.Nonempty ∧
      (∑ a ∈ S, record n q bus a) = 0) := by
  classical
  constructor
  · by_cases hne : (Section n q bus).Nonempty
    · have hvne : (uniformValues n q bus).Nonempty := convexHull_nonempty_iff.mp
        ⟨hne.choose, section_mem_hull n q bus hq _ hne.choose_spec⟩
      have hf := uniform_values_finite n q bus
      obtain ⟨l, hl, hmin⟩ := Set.exists_min_image (uniformValues n q bus) id hf hvne
      obtain ⟨r, hr, hmax⟩ := Set.exists_min_image (β := OrderDual ℝ)
        (uniformValues n q bus) id hf hvne
      have hval : uniformValues n q bus ⊆ Set.Icc l r := fun z hz => ⟨hmin z hz, hmax z hz⟩
      have hmem (z : ℝ) (hz : z ∈ uniformValues n q bus) : z ∈ Section n q bus := by
        obtain ⟨S, e, hc, rfl⟩ := hz
        exact uniform_mem_section n q bus S e hc
      have hep (z : ℝ) (hz : z ∈ uniformValues n q bus) : UniformEndpoint n q bus z := by
        obtain ⟨S, e, hc, hze⟩ := hz
        refine ⟨S, e, hc, hze, hc.1.card_pos, ?_⟩
        simpa only [HannRouterDephasing.address_card] using Finset.card_le_univ S
      right
      refine ⟨l, r, hmin r hr, ?_, hep l hl, hep r hr⟩
      apply Set.Subset.antisymm
      · intro z hz
        exact convexHull_min hval (convex_Icc l r) (section_mem_hull n q bus hq z hz)
      · exact (section_convex n q bus).ordConnected.out (hmem l hl) (hmem r hr)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)
  · rintro ⟨p, hp, hm, hz⟩
    obtain ⟨S, hs, _, he⟩ := zero_certificate n q bus hq p hp hm (by simpa using hz)
    exact ⟨S, hs, he⟩

end D5.S3.Quantum.Routing.HannUniformSection
