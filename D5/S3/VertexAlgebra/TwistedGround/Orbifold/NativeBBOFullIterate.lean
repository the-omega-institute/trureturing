import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIterateLocality

/-! Identification of the finite tilted residue with the actual BB iterate
on both native sectors; recovery of the signed law at all integer labels. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate

open ActualLeechHyperbolic (leechData)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd OddCarrier oddMode)
open NativeBBOCoefficientTransport (P Q bb ab fixedH mixedImageSpan_eq_top bboDefect
  bboDefect_eq_zero_iff_jacobi)
open NativeBBOIntegerLocality NativeBBOIterateLocality
open FieldNormalProductLocality (deltaEnd)
open LatticeHalfFockGroundRightCurrentTransport (residueWeight)
open LatticeHalfFockGroundRightCurrentTransport.Calculus
  (R Z Valid Q_mode valid_of_locality recover_full fullLaw leftTerm firstTerm secondTerm)
open private Z_mode ext_modes from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private finite_convolution from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open private p_tail from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier leechData
local notation "comm" => FieldNormalProductLocality.commutator
local notation "Tilt" => LatticeHalfFockGroundRightCurrentTransport.Calculus.Q

private theorem Z_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X : VertexOperator ℂ V) : Z 0 X = X := by
  apply ext_modes
  intro n
  rw [Z_mode, sub_zero]

private theorem Z_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c d : ℤ) (X : VertexOperator ℂ V) : Z c (Z d X) = Z (c+d) X := by
  apply ext_modes
  intro n
  simp only [Z_mode]
  rw [sub_sub]

set_option maxHeartbeats 1000000 in
/-- BBH and the inverse half-binomial convolution fix the tilted iterate
on every vector in the even twisted sector. -/
-- The native fixed-field coefficient and product-carrier instances require extra elaboration.
theorem T_on_H (b c : B) (r : ℤ) (N : ℕ)
    (tail : ∀ t : ℤ, (N : ℤ) ≤ t → bb b c t = 0)
    (m : ℤ) (h : H) :
    ((T b c r N)[[m]]) (h, 0) = ((G (bb b c r))[[m]]) (h, 0) := by
  let J := ((N : ℤ)-r).toNat
  let v (k : ℕ) : W := ((G (bb b c (r+k)))[[m-k]]) (h, 0)
  have hv (k : ℕ) (hk : J ≤ k) : v k = 0 := by
    dsimp [v]
    rw [tail _ (by dsimp [J] at hk; omega), G_zero]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  have row (ell : ℕ) : ((R (F b) (F c) (r+ell))[[m-1-ell]]) (h, 0) =
      ∑ k ∈ Finset.range J, Ring.choose (1/2 : ℂ) k • v (ell+k) := by
    have he := bbh_residue b c h 0 (m-1-ell) (r+ell)
    rw [neg_zero, Z_zero] at he
    simp only [Int.cast_zero, zero_add, add_zero] at he
    rw [he]
    have hf : (∑ᶠ j : ℕ, Ring.choose (1/2 : ℂ) j •
          fixedH (bb b c (r+ell+j)) (m-1-ell+1-j) h) =
        ∑ j ∈ Finset.range J, Ring.choose (1/2 : ℂ) j •
          fixedH (bb b c (r+ell+j)) (m-1-ell+1-j) h := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hn
      have hj' : J ≤ j := by simpa using hn
      have hh := congrArg Prod.fst (hv (ell+j) (by omega))
      simp only [v, G_mode, Prod.fst_zero, Nat.cast_add] at hh
      apply hj
      change Ring.choose (1/2 : ℂ) j • fixedH (bb b c (r+ell+j)) (m-1-ell+1-j) h = 0
      rw [show r+(ell:ℤ)+j = r+((ell:ℤ)+j) by omega,
        show m-1-(ell:ℤ)+1-j = m-((ell:ℤ)+j) by omega, hh, smul_zero]
    rw [hf]
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst, v, G_mode, Nat.cast_add]
      apply Finset.sum_congr rfl
      intro j _
      rw [show r+(ell:ℤ)+j = r+((ell:ℤ)+j) by omega,
        show m-1-(ell:ℤ)+1-j = m-((ell:ℤ)+j) by omega]
    · simp only [Prod.snd_sum, Prod.smul_snd, v, G_mode, map_zero,
        smul_zero, Finset.sum_const_zero]
  rw [T, Z_mode, Q_mode]
  simp only [Int.cast_one]
  calc
    _ = ∑ ell ∈ Finset.range J, Ring.choose (-(1 : ℂ)/2) ell •
        (∑ k ∈ Finset.range J, Ring.choose (1/2 : ℂ) k • v (ell+k)) := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [row]
    _ = ∑ k ∈ Finset.range J, Ring.choose (0 : ℂ) k • v k := by
      simpa only [show -(1 : ℂ)/2 + 1/2 = 0 by ring] using
        (finite_convolution (-(1 : ℂ)/2) (1/2) J v hv)
    _ = v 0 := by
      by_cases hJ : J = 0
      · rw [hJ, Finset.range_zero, Finset.sum_empty]
        exact (hv 0 (by omega)).symm
      · rw [Finset.sum_eq_single 0]
        · rw [Ring.choose_zero_right, one_smul]
        · intro j hj hne
          rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hne), zero_smul]
        · intro hz
          exact False.elim (hJ (by simpa using hz))
    _ = _ := by simp only [v, Nat.cast_zero, add_zero, sub_zero]

/-- The finite tilted residue is the actual fixed iterate on the entire
native carrier. Its difference kills the complementary twisted sector;
locality transports that zero along every mixed coefficient. -/
theorem T_eq_actual (b c : B) (r : ℤ) (N : ℕ)
    (tail : ∀ t : ℤ, (N : ℤ) ≤ t → bb b c t = 0) :
    T b c r N = G (bb b c r) := by
  let a := bb b c r
  let D := T b c r N - G a
  have hD (m : ℤ) (h : H) : (D[[m]]) (h, 0) = 0 := by
    simp only [D, map_sub, Pi.sub_apply, LinearMap.sub_apply]
    rw [T_on_H b c r N tail, sub_self]
  have gen (d : B) (h : H) (s m : ℤ) : (D[[m]]) (0, P d s h) = 0 := by
    obtain ⟨K₀, hK₀⟩ := T_locality b c d r N
    obtain ⟨L, hL⟩ := ab_tail a d
    let K := max K₀ L
    have hT : (deltaEnd ^ K) (comm (T b c r N) (F d)) = 0 :=
      raise_locality _ (le_max_left K₀ L) hK₀
    have hA (t u : ℤ) : ((deltaEnd ^ K) (comm (G a) (F d))) t u (h, 0) = 0 :=
      mixed_locality_on_H a d K (fun n hn => hL n (by dsimp [K] at hn; omega)) t u h
    have hcomm : comm D (F d) = comm (T b c r N) (F d) - comm (G a) (F d) := by
      funext t u
      simp only [D, FieldNormalProductLocality.commutator, map_sub, Pi.sub_apply, sub_mul, mul_sub]
      abel
    have poly (t u : ℤ) : ∑ j ∈ Finset.range (K+1),
        ((-1 : ℂ)^j * (K.choose j : ℂ)) •
          (D[[t+(K:ℤ)-j]]) (0, P d (u+j) h) = 0 := by
      have he : ((deltaEnd ^ K) (comm D (F d))) t u (h, 0) = 0 := by
        rw [hcomm, map_sub, hT]
        simp only [Pi.sub_apply, LinearMap.sub_apply, Pi.zero_apply, LinearMap.zero_apply,
          hA, sub_zero]
      rw [FieldDeltaBinomial.delta_binomial] at he
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply,
        FieldNormalProductLocality.commutator, Module.End.mul_apply,
        LinearMap.sub_apply, hD, F_mode, map_zero, neg_zero, sub_zero] using he
    obtain ⟨S, hS⟩ := p_tail d h
    have descend (k : ℕ) : ∀ s : ℤ, (S-s).toNat = k → ∀ m : ℤ,
        (D[[m]]) (0, P d s h) = 0 := by
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro s hs m
        by_cases hhigh : S ≤ s
        · rw [hS s hhigh]
          change (D[[m]]) (0 : W) = 0
          exact map_zero _
        have hp := poly (m-K) s
        simp only [show ∀ j : ℕ, m-(K:ℤ)+K-j = m-j by intro; omega] at hp
        rw [Finset.sum_eq_single 0] at hp
        · simpa using hp
        · intro j hj hne
          have hj' : 0 < j := Nat.pos_of_ne_zero hne
          rw [ih (S-(s+j)).toNat (by omega) (s+j) rfl (m-j), smul_zero]
        · intro hz
          exact False.elim (hz (Finset.mem_range.mpr (by omega)))
    exact descend _ s rfl m
  apply ext_modes
  intro m
  apply LinearMap.ext
  intro x
  have hz : (D[[m]]) x = 0 := by
    let E : O →ₗ[ℂ] W := (D[[m]]).comp (LinearMap.inr ℂ H O)
    have hle : NativeMixedPairBorcherds.mixedImageSpan ≤ LinearMap.ker E := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨s, d, h⟩, rfl⟩
      exact gen d h s m
    rw [mixedImageSpan_eq_top] at hle
    have ho : (D[[m]]) (0, x.2) = 0 := hle (Submodule.mem_top (x := x.2))
    have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
    rw [hx, map_add, hD, ho, add_zero]
  simp only [D, map_sub, Pi.sub_apply, LinearMap.sub_apply] at hz
  exact sub_eq_zero.mp hz

set_option maxHeartbeats 1000000 in
/-- All three mode labels of the native signed BBO Jacobi identity, with the
actual BB iterate and the two original ordered products. -/
-- The exact native coefficient readout requires extra elaboration of the sector instances.
theorem bboDefect_eq_zero (b c : B) (p q r : ℤ) : bboDefect b c p q r = 0 := by
  obtain ⟨N, tail, hloc⟩ := pair_locality b c
  let U (t : ℤ) := Z (-1) (G (bb b c t))
  have htail (t : ℤ) (ht : (N : ℤ) ≤ t) : U t = 0 := by
    dsimp [U]
    rw [tail t ht, G_zero]
    apply ext_modes
    intro n
    simp [Z_mode]
  have hinv (t : ℤ) : U t = Tilt (F b) (F c) 1 t N := by
    dsimp [U]
    rw [← T_eq_actual b c t N tail, T, Z_comp, show (-1 : ℤ)+1 = 0 by norm_num, Z_zero]
  have law := recover_full (F b) (F c) U 1 N N htail
    (fun t => valid_of_locality _ _ N (locality_shift _ _ N (-t) hloc))
    (valid_of_locality _ _ N hloc) hinv
  apply LinearMap.ext
  intro o
  change bboDefect b c p q r o = 0
  apply (bboDefect_eq_zero_iff_jacobi b c o p q r).2
  obtain ⟨hleft, hfirst, hsecond, he⟩ := law q p r (0,o)
  have hh := congrArg (LinearMap.snd ℂ H O) he
  change (LinearMap.snd ℂ H O) (∑ᶠ j, leftTerm U 1 q p r (0,o) j) =
    (LinearMap.snd ℂ H O) ((∑ᶠ j, firstTerm (F b) (F c) q p r (0,o) j) -
      (∑ᶠ j, secondTerm (F b) (F c) q p r (0,o) j)) at hh
  rw [map_sub, map_finsum _ hleft, map_finsum _ hfirst, map_finsum _ hsecond] at hh
  simp only [leftTerm, firstTerm, secondTerm, U, Z_mode, G_mode, F_mode,
    residueWeight, LinearMap.snd_apply, Prod.smul_snd, map_zero, neg_zero, map_neg,
    smul_neg, finsum_neg_distrib, sub_neg_eq_add, smul_smul, Int.cast_one,
    show ∀ j : ℕ, q+p-j-(-1) = p+q+1-j by intro; omega] at hh
  change -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      P b (q+r-j) (Q c (p+j) o)) +
    (∑ᶠ j : ℕ, ((-1 : ℂ)^(r+(j:ℤ)) * Ring.choose (r : ℂ) j) •
      P c (p+r-j) (Q b (q+j) o)) =
    ∑ᶠ j : ℕ, Ring.choose ((q : ℂ)+1/2) j •
      oddMode leechData (bb b c (r+j)) (p+q+1-j) o
  simp only [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, mul_assoc]
  simp only [mul_comm ((-1 : ℂ)^r)]
  exact hh.symm

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate.T_eq_actual' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms T_eq_actual

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate.bboDefect_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bboDefect_eq_zero

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate
