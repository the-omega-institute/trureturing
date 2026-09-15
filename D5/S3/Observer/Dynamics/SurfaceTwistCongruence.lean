/- GID: D5/S3/Observer/Dynamics/SurfaceTwistCongruence
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/SurfaceTwistCongruence
   mirror-E: none(waiver:all-genera-characteristic-quotient-construction)
   anchors: []
   utility: none
   digest: A fully invariant finite quotient of the actual surface presentation detects precisely the multiples of every prescribed separating-twist power. -/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
The source object is the standard presentation with genus extra+2. The map
called twist conjugates the first handle by its boundary commutator and fixes
the other handles. Its inverse is constructed; powers are actual iterates of
this one endomorphism. No surface-group relation, finite quotient, characteristic
kernel, finite order or detection property is supplied as a hypothesis.

The finite target has rotation order 4m and total order 8m. The detector is the
image of simultaneous evaluation at ALL homomorphisms to this target. This
ensures full invariance of its kernel, rather than assuming a chosen dihedral
representation has characteristic kernel. The essential lower bound excludes
one common inner conjugation of the WHOLE representation, not separate
conjugacies of generator images.

This is a source-reviewed candidate, not a claimed kernel-checked declaration.
Prior-art context: Klukowski, arXiv:2411.06867v2, Definition 3, Corollary 7,
Theorem 8, Conjecture 13. The qualitative cyclic subgroup consequence is known;
the content pursued here is the explicit target, canonical finite quotient,
and matching all-power upper and lower bounds. No resolution of Conjecture 13
or identification of a topological homeomorphism with this presentation map
is claimed. The pinned upstream is mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Observer.Dynamics.SurfaceTwistCongruence

/-- Four distinguished generators and two for every additional handle. -/
abbrev Generator (extra : ℕ) := Fin 4 ⊕ (Fin extra × Fin 2)

/-- The chosen commutator convention throughout the construction. -/
def bracket {G : Type*} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

/-- The ordered product of the additional-handle commutators. -/
def extraWord (extra : ℕ) : FreeGroup (Generator extra) :=
  ((List.finRange extra).map fun i =>
    bracket (FreeGroup.of (Sum.inr (i, 0))) (FreeGroup.of (Sum.inr (i, 1)))).prod

/-- The actual closed orientable genus-(extra+2) surface relator. -/
def surfaceRelator (extra : ℕ) : FreeGroup (Generator extra) :=
  bracket (FreeGroup.of (Sum.inl 0)) (FreeGroup.of (Sum.inl 1)) *
    bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3)) * extraWord extra

abbrev Surface (extra : ℕ) :=
  PresentedGroup ({surfaceRelator extra} : Set (FreeGroup (Generator extra)))

/-- The actual generators of the presented quotient, not a free replacement. -/
def generator (extra : ℕ) (i : Generator extra) : Surface extra := PresentedGroup.of i

def boundary (extra : ℕ) : Surface extra :=
  bracket (generator extra (Sum.inl 0)) (generator extra (Sum.inl 1))

/-- Images of the presentation generators for a signed twist. -/
def twistImages (extra : ℕ) (s : ℤ) : Generator extra → Surface extra
  | Sum.inl i => if i.val < 2 then
      boundary extra ^ s * generator extra (Sum.inl i) * (boundary extra ^ s)⁻¹
    else generator extra (Sum.inl i)
  | Sum.inr i => generator extra (Sum.inr i)

/-- A signed twist on the original presentation, obtained by checking its relator. -/
def twistHom (extra : ℕ) (s : ℤ) : Surface extra →* Surface extra := by
  let F := FreeGroup.lift (twistImages extra s)
  let p := PresentedGroup.mk ({surfaceRelator extra} : Set (FreeGroup (Generator extra)))
  have hrel : p (surfaceRelator extra) = 1 :=
    PresentedGroup.one_of_mem (by simp)
  have htail : F (extraWord extra) = p (extraWord extra) := by
    unfold extraWord
    generalize List.finRange extra = xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, ih]
        congr 1
  have hfirst : F
      (bracket (FreeGroup.of (Sum.inl 0)) (FreeGroup.of (Sum.inl 1))) =
      boundary extra := by
    simp only [F, bracket, map_mul, map_inv, FreeGroup.lift_apply_of]
    change
      (boundary extra ^ s * generator extra (Sum.inl 0) * (boundary extra ^ s)⁻¹) *
      (boundary extra ^ s * generator extra (Sum.inl 1) * (boundary extra ^ s)⁻¹) *
      (boundary extra ^ s * generator extra (Sum.inl 0) * (boundary extra ^ s)⁻¹)⁻¹ *
      (boundary extra ^ s * generator extra (Sum.inl 1) * (boundary extra ^ s)⁻¹)⁻¹ = _
    calc
      _ = boundary extra ^ s * boundary extra * (boundary extra ^ s)⁻¹ := by
        dsimp [boundary, bracket]
        group
      _ = boundary extra := by group
  apply PresentedGroup.toGroup (f := twistImages extra s)
  intro w hw
  rcases Set.mem_singleton_iff.mp hw with rfl
  change F (surfaceRelator extra) = 1
  change F ((bracket (FreeGroup.of (Sum.inl 0)) (FreeGroup.of (Sum.inl 1))) *
    bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3)) * extraWord extra) = 1
  rw [map_mul, map_mul, hfirst, htail]
  have hsecond : F
      (bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3))) =
      p (bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3))) := by
    simp [F, p, bracket, twistImages, generator, PresentedGroup.of]
  rw [hsecond]
  change p ((bracket (FreeGroup.of (Sum.inl 0)) (FreeGroup.of (Sum.inl 1))) *
    bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3)) * extraWord extra) = 1 at hrel
  simpa only [boundary, bracket, generator, PresentedGroup.of, map_mul, map_inv] using hrel

/-- Genuine repeated composition of the single step. -/
def twistPower (extra : ℕ) : ℕ → Surface extra →* Surface extra
  | 0 => MonoidHom.id _
  | n + 1 => (twistHom extra 1).comp (twistPower extra n)

abbrev Target (m : ℕ) := DihedralGroup (4 * m)
abbrev Representation (extra m : ℕ) := Surface extra →* Target m

/-- Simultaneous evaluation at every finite-target representation. -/
def evaluation (extra m : ℕ) : Surface extra →* (Representation extra m → Target m) where
  toFun x ρ := ρ x
  map_one' := by funext ρ; exact map_one ρ
  map_mul' x y := by funext ρ; exact map_mul ρ x y

/-- An actual subgroup of a finite product; the projection is onto its image. -/
abbrev Detector (extra m : ℕ) := (evaluation extra m).range

def projection (extra m : ℕ) : Surface extra →* Detector extra m :=
  (evaluation extra m).rangeRestrict

/-- A mixed word using one generator on each side of the separating curve. -/
def crossingWord (extra : ℕ) : Surface extra :=
  generator extra (Sum.inl 0) * (generator extra (Sum.inl 3))⁻¹

/-- Finite characteristic detection of all powers, with an exact outer period.
The last clause records complete blindness of every abelian representation.
The innerness clause is the literal condition for the induced automorphism on
the surjective quotient to be inner, including the same conjugator for all x. -/
theorem finite_characteristic_twist_detector (extra m : ℕ) (hm : 0 < m) :
    Finite (Detector extra m) ∧
    Function.Surjective (projection extra m) ∧
    (∀ f : Surface extra →* Surface extra, ∀ x,
      projection extra m x = 1 → projection extra m (f x) = 1) ∧
    Function.Bijective (twistHom extra 1) ∧
    (∀ n : ℕ,
      (∃ z : Detector extra m, ∀ x : Surface extra,
        projection extra m (twistPower extra n x) =
          z * projection extra m x * z⁻¹) ↔ m ∣ n) ∧
    (∀ n : ℕ,
      (∃ z : Detector extra m,
        projection extra m (twistPower extra n (crossingWord extra)) =
          z * projection extra m (crossingWord extra) * z⁻¹) ↔ m ∣ n) ∧
    (∀ n : ℕ, m ∣ n → ∀ x : Surface extra,
      projection extra m (twistPower extra n x) = projection extra m x) ∧
    (∀ (A : Type) [CommGroup A] (f : Surface extra →* A),
      f.comp (twistHom extra 1) = f) := by
  classical
  letI : NeZero (4 * m) := ⟨by omega⟩
  have hgens : ∀ (s : ℤ) (i : Generator extra),
      twistHom extra s (generator extra i) = twistImages extra s i := by
    intro s i
    simp only [twistHom, generator, PresentedGroup.toGroup.of]
  have hboundary : ∀ s : ℤ, twistHom extra s (boundary extra) = boundary extra := by
    intro s
    unfold boundary bracket
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      hgens s (Sum.inl 0), hgens s (Sum.inl 1)]
    simp only [twistImages]
    change
      (boundary extra ^ s * generator extra (Sum.inl 0) * (boundary extra ^ s)⁻¹) *
      (boundary extra ^ s * generator extra (Sum.inl 1) * (boundary extra ^ s)⁻¹) *
      (boundary extra ^ s * generator extra (Sum.inl 0) * (boundary extra ^ s)⁻¹)⁻¹ *
      (boundary extra ^ s * generator extra (Sum.inl 1) * (boundary extra ^ s)⁻¹)⁻¹ = _
    calc
      _ = boundary extra ^ s * boundary extra * (boundary extra ^ s)⁻¹ := by
        dsimp [boundary, bracket]
        group
      _ = boundary extra := by group
  have hinverse : ∀ s : ℤ,
      (twistHom extra (-s)).comp (twistHom extra s) = MonoidHom.id _ := by
    intro s
    apply PresentedGroup.ext
    intro i
    change twistHom extra (-s) (twistHom extra s (generator extra i)) = generator extra i
    rw [hgens]
    rcases i with i | i
    · fin_cases i <;>
        simp [twistImages, map_mul, map_inv, map_zpow, hboundary, hgens] <;> group
    · simp [twistImages, hgens]
  have hbijective : Function.Bijective (twistHom extra 1) := by
    constructor
    · intro x y h
      have hx := congrArg (fun f : Surface extra →* Surface extra => f x) (hinverse 1)
      have hy := congrArg (fun f : Surface extra →* Surface extra => f y) (hinverse 1)
      change twistHom extra (-1) (twistHom extra 1 x) = x at hx
      change twistHom extra (-1) (twistHom extra 1 y) = y at hy
      exact hx.symm.trans ((congrArg (twistHom extra (-1)) h).trans hy)
    · intro y
      refine ⟨twistHom extra (-1) y, ?_⟩
      have h := congrArg (fun f : Surface extra →* Surface extra => f y) (hinverse (-1))
      simpa using h
  have hpower : ∀ n : ℕ, ∀ i : Generator extra,
      twistPower extra n (generator extra i) =
        match i with
        | Sum.inl j => if j.val < 2 then
            boundary extra ^ n * generator extra i * (boundary extra ^ n)⁻¹
          else generator extra i
        | Sum.inr _ => generator extra i := by
    intro n
    induction n with
    | zero => intro i; cases i <;> simp [twistPower]
    | succ n ih =>
        intro i
        change twistHom extra 1 (twistPower extra n (generator extra i)) = _
        rw [ih]
        rcases i with i | i
        · fin_cases i <;>
            simp [map_mul, map_inv, map_pow, hboundary, hgens, twistImages, pow_succ] <;> group
        · simp [hgens, twistImages]
  have hfiniteReps : Finite (Representation extra m) :=
    Finite.of_injective
      (fun ρ : Representation extra m => fun i : Generator extra => ρ (generator extra i))
      (by
        intro ρ σ h
        apply PresentedGroup.ext
        intro i
        exact congrFun h i)
  letI := hfiniteReps
  have hfinite : Finite (Detector extra m) := inferInstance
  have hsurj : Function.Surjective (projection extra m) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hinvariant : ∀ f : Surface extra →* Surface extra, ∀ x,
      projection extra m x = 1 → projection extra m (f x) = 1 := by
    intro f x hx
    apply Subtype.ext
    funext ρ
    have h := congrArg (fun z : Detector extra m => z.1 (ρ.comp f)) hx
    exact h
  -- The universal period is established for every finite-target representation.
  have hcomm : ∀ a b : Target m, ∃ t : ZMod (4 * m),
      bracket a b = DihedralGroup.r (2 * t) := by
    rintro (a | a) (b | b)
    · exact ⟨0, by simp [bracket]⟩
    · exact ⟨a, by simp [bracket] <;> congr 1 <;> ring⟩
    · exact ⟨-b, by simp [bracket] <;> congr 1 <;> ring⟩
    · exact ⟨b-a, by simp [bracket] <;> congr 1 <;> ring⟩
  have hcentral : ∀ a b y : Target m, ∀ n : ℕ, m ∣ n →
      bracket a b ^ n * y * (bracket a b ^ n)⁻¹ = y := by
    intro a b y n hn
    obtain ⟨j, rfl⟩ := hn
    obtain ⟨t, ht⟩ := hcomm a b
    rw [ht]
    have hz : (4 : ZMod (4 * m)) * (m : ZMod (4 * m)) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (4 * m)
    rcases y with y | y
    · simp <;> congr 1 <;> ring
    · simp only [DihedralGroup.r_pow, DihedralGroup.r_mul_sr,
        DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
      congr 1
      push_cast
      linear_combination -(t * (j : ZMod (4 * m))) * hz
  have hperiod : ∀ n : ℕ, m ∣ n → ∀ ρ : Representation extra m,
      ρ.comp (twistPower extra n) = ρ := by
    intro n hn ρ
    apply PresentedGroup.ext
    intro i
    change ρ (twistPower extra n (generator extra i)) = ρ (generator extra i)
    rw [hpower]
    rcases i with i | i
    · by_cases hi : i.val < 2
      · simp only [hi, if_true, map_mul, map_inv, map_pow]
        have hb : ρ (boundary extra) =
            bracket (ρ (generator extra (Sum.inl 0))) (ρ (generator extra (Sum.inl 1))) := by
          simp [boundary, bracket]
        rw [hb]
        exact hcentral _ _ _ n hn
      · simp [hi]
    · rfl
  have hquotientPeriod : ∀ n : ℕ, m ∣ n → ∀ x : Surface extra,
      projection extra m (twistPower extra n x) = projection extra m x := by
    intro n hn x
    apply Subtype.ext
    funext ρ
    exact congrArg (fun f : Representation extra m => f x) (hperiod n hn ρ)
  -- A single explicitly relator-compatible representation gives the matching lower bound.
  let images : Generator extra → Target m := fun i =>
    match i with
    | Sum.inl j => ![DihedralGroup.sr 0, DihedralGroup.r 1,
        DihedralGroup.r 1, DihedralGroup.sr 0] j
    | Sum.inr _ => 1
  have htargetRel : ∀ w ∈ ({surfaceRelator extra} : Set (FreeGroup (Generator extra))),
      FreeGroup.lift images w = 1 := by
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    have htail : FreeGroup.lift images (extraWord extra) = 1 := by
      unfold extraWord
      generalize List.finRange extra = xs
      induction xs with
      | nil => simp
      | cons i xs ih =>
          simp only [List.map_cons, List.prod_cons, map_mul, ih]
          simp [bracket, images]
    simp [surfaceRelator, map_mul, bracket, htail, images]
  let ρ : Representation extra m := PresentedGroup.toGroup htargetRel
  have hrho : ∀ i, ρ (generator extra i) = images i := by
    intro i
    exact PresentedGroup.toGroup.of _
  have hrhoBoundary : ρ (boundary extra) = DihedralGroup.r (-2) := by
    simp [boundary, bracket, hrho, images]
    ring
  have hfirst : ∀ n : ℕ,
      ρ (twistPower extra n (generator extra (Sum.inl 0))) =
        DihedralGroup.sr (4 * (n : ZMod (4 * m))) := by
    intro n
    rw [hpower]
    change ρ (boundary extra ^ n * generator extra (Sum.inl 0) *
      (boundary extra ^ n)⁻¹) = _
    rw [map_mul, map_mul, map_inv, map_pow, hrhoBoundary, hrho]
    change (DihedralGroup.r (-2) : Target m) ^ n * DihedralGroup.sr 0 *
      ((DihedralGroup.r (-2) : Target m) ^ n)⁻¹ = _
    simp only [DihedralGroup.r_pow, DihedralGroup.r_mul_sr,
      DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
    congr 1
    ring
  have hfixed : ∀ n : ℕ,
      ρ (twistPower extra n (generator extra (Sum.inl 3))) = DihedralGroup.sr 0 := by
    intro n
    rw [hpower]
    simp [hrho, images]
  have houter : ∀ n : ℕ,
      (∃ z : Detector extra m, ∀ x : Surface extra,
        projection extra m (twistPower extra n x) = z * projection extra m x * z⁻¹) ↔ m ∣ n := by
    intro n
    constructor
    · rintro ⟨z, hz⟩
      have ha := congrArg (fun u : Detector extra m => u.1 ρ) (hz (generator extra (Sum.inl 0)))
      have hd := congrArg (fun u : Detector extra m => u.1 ρ) (hz (generator extra (Sum.inl 3)))
      change ρ (twistPower extra n (generator extra (Sum.inl 0))) =
        z.1 ρ * ρ (generator extra (Sum.inl 0)) * (z.1 ρ)⁻¹ at ha
      change ρ (twistPower extra n (generator extra (Sum.inl 3))) =
        z.1 ρ * ρ (generator extra (Sum.inl 3)) * (z.1 ρ)⁻¹ at hd
      rw [hfirst, hrho] at ha
      rw [hfixed, hrho] at hd
      have heq : DihedralGroup.sr (4 * (n : ZMod (4 * m))) = DihedralGroup.sr 0 := by
        exact ha.trans hd.symm
      have hzero : ((4 * n : ℕ) : ZMod (4 * m)) = 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using DihedralGroup.sr.inj heq
      have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
      obtain ⟨j, hj⟩ := hdiv
      refine ⟨j, ?_⟩
      nlinarith [hj]
    · intro hn
      refine ⟨1, ?_⟩
      intro x
      simpa using hquotientPeriod n hn x
  have hword : ∀ n : ℕ,
      (∃ z : Detector extra m,
        projection extra m (twistPower extra n (crossingWord extra)) =
          z * projection extra m (crossingWord extra) * z⁻¹) ↔ m ∣ n := by
    intro n
    constructor
    · rintro ⟨z, hz⟩
      have h := congrArg (fun u : Detector extra m => u.1 ρ) hz
      change ρ (twistPower extra n (crossingWord extra)) =
        z.1 ρ * ρ (crossingWord extra) * (z.1 ρ)⁻¹ at h
      have hzeroWord : ρ (crossingWord extra) = 1 := by
        simp [crossingWord, hrho, images]
      have htwistedWord : ρ (twistPower extra n (crossingWord extra)) =
          DihedralGroup.r (-4 * (n : ZMod (4 * m))) := by
        simp only [crossingWord, map_mul, map_inv, hfirst, hfixed,
          DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
        congr 1
        ring
      rw [htwistedWord, hzeroWord] at h
      have heq : DihedralGroup.r (-4 * (n : ZMod (4 * m))) = DihedralGroup.r 0 := by
        simpa using h
      have hnzero : ((4 * n : ℕ) : ZMod (4 * m)) = 0 := by
        have hi := DihedralGroup.r.inj heq
        push_cast
        linear_combination -hi
      obtain ⟨j, hj⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hnzero
      exact ⟨j, by nlinarith [hj]⟩
    · intro hn
      exact ⟨1, by simpa using hquotientPeriod n hn (crossingWord extra)⟩
  have hab : ∀ (A : Type) [CommGroup A] (f : Surface extra →* A),
      f.comp (twistHom extra 1) = f := by
    intro A _ f
    apply PresentedGroup.ext
    intro i
    change f (twistHom extra 1 (generator extra i)) = f (generator extra i)
    rw [hgens]
    have hb : f (boundary extra) = 1 := by
      simp [boundary, bracket, mul_comm, mul_left_comm, mul_assoc]
    rcases i with i | i
    · fin_cases i <;> simp [twistImages, map_mul, map_inv, map_zpow, hb]
    · rfl
  exact ⟨hfinite, hsurj, hinvariant, hbijective, houter, hword, hquotientPeriod, hab⟩

#print axioms finite_characteristic_twist_detector

end D5.S3.Observer.Dynamics.SurfaceTwistCongruence
