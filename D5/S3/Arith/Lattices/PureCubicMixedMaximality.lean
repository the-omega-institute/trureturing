/- GID: D5/S3/Arith/Lattices/PureCubicMixedMaximality
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicMixedMaximality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The mixed pure-cubic lattice is the full integer ring, with field discriminant. -/

import D5.S3.Arith.Lattices.PureCubicIntegralLattices
import D5.S3.Arith.Lattices.PureCubicThreeSaturation
import D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicMixedMaximality

open Polynomial Algebra Module
open scoped NumberField

/-- For coprime positive squarefree radicands, the mixed lattice is the
integer ring and its discriminant is the field discriminant. -/
theorem pure_cubic_mixed_maximality_and_discriminant
    {K : Type*} [Field K] [NumberField K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hmsq : Squarefree m) (hnsq : Squarefree n) (hcop : IsCoprime m n)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k) :
    (∀ z : K, IsIntegral ℤ z ↔ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3)) ∧
    NumberField.discr K = -3 * (m * n) ^ 2 := by
  have hm : m ≠ 0 := ne_of_gt hmpos
  have hn : n ≠ 0 := ne_of_gt hnpos
  have hmax : ∀ z : K, IsIntegral ℤ z → ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3) := by
    letI : Module.Finite ℚ K := pb.finite
    let gamma : K :=
      (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3
    let S : Set K := {x | ∃ u r s : ℤ,
      x = (u : K) + (r : K) * pb.gen + (s : K) * gamma}
    have hS_add {x y : K} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by
      obtain ⟨u, r, s, rfl⟩ := hx
      obtain ⟨u', r', s', rfl⟩ := hy
      refine ⟨u + u', r + r', s + s', ?_⟩
      push_cast
      ring
    have hS_smul (d : ℤ) {x : K} (hx : x ∈ S) : (d : K) * x ∈ S := by
      obtain ⟨u, r, s, rfl⟩ := hx
      refine ⟨d * u, d * r, d * s, ?_⟩
      push_cast
      ring
    have hmin : minpoly ℚ pb.gen =
        (Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C ((m * n ^ 2 : ℤ) : ℚ) := by
      have heval : Polynomial.aeval pb.gen
          ((Polynomial.X : Polynomial ℚ) ^ 3 -
            Polynomial.C ((m * n ^ 2 : ℤ) : ℚ)) = 0 := by
        simpa using sub_eq_zero.mpr hroot
      have hdegree :
          (((Polynomial.X : Polynomial ℚ) ^ 3 -
            Polynomial.C ((m * n ^ 2 : ℤ) : ℚ))).degree ≤
            (minpoly ℚ pb.gen).degree := by
        rw [Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 3),
          Polynomial.degree_eq_natDegree (minpoly.ne_zero pb.isIntegral_gen),
          pb.natDegree_minpoly, h3]
      exact (minpoly.unique_of_degree_le_degree_minpoly ℚ pb.gen
        (Polynomial.monic_X_pow_sub_C _ (by norm_num : 3 ≠ 0))
        heval hdegree).symm
    have hnormGeneric (d : ℤ)
        (hd : minpoly ℚ pb.gen =
          (Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (d : ℚ)) :
        Algebra.norm ℚ pb.gen = (d : ℚ) := by
      rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hd, h3]
      simp <;> norm_num
    have hnorm : Algebra.norm ℚ pb.gen = ((m * n ^ 2 : ℤ) : ℚ) :=
      hnormGeneric (m * n ^ 2) hmin
    have hderiv :
        ((Polynomial.X : Polynomial ℚ) ^ 3 -
          Polynomial.C ((m * n ^ 2 : ℤ) : ℚ)).derivative =
          Polynomial.C 3 * Polynomial.X ^ 2 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
        Polynomial.derivative_X_pow]
      norm_num
    have hdisc : Algebra.discr ℚ pb.basis =
        -27 * (((m * n ^ 2 : ℤ) : ℚ)) ^ 2 := by
      rw [Algebra.discr_powerBasis_eq_norm, hmin, hderiv]
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      rw [Algebra.norm_algebraMap, hnorm, pb.finrank, h3]
      norm_num
    have hAlphaInt : IsIntegral ℤ pb.gen := by
      obtain ⟨ha, _, _, _, _, _, _, _, _⟩ :=
        D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices
          pb h3 m n c a k v hm hn hv hroot hcubic hcv
      exact ha
    have hspan {y : K} (hy : y ∈ adjoin ℤ ({pb.gen} : Set K)) :
        ∃ u r s : ℤ,
          y = (u : K) + (r : K) * pb.gen + (s : K) * pb.gen ^ 2 := by
      let T : Subring K := {
        carrier := {x | ∃ u r s : ℤ,
          x = (u : K) + (r : K) * pb.gen + (s : K) * pb.gen ^ 2}
        zero_mem' := ⟨0, 0, 0, by simp⟩
        one_mem' := ⟨1, 0, 0, by simp⟩
        add_mem' := by
          intro x y hx hy
          obtain ⟨u, r, s, rfl⟩ := hx
          obtain ⟨u', r', s', rfl⟩ := hy
          refine ⟨u + u', r + r', s + s', ?_⟩
          push_cast
          ring
        neg_mem' := by
          intro x hx
          obtain ⟨u, r, s, rfl⟩ := hx
          refine ⟨-u, -r, -s, ?_⟩
          push_cast
          ring
        mul_mem' := by
          intro x y hx hy
          obtain ⟨u, r, s, rfl⟩ := hx
          obtain ⟨u', r', s', rfl⟩ := hy
          refine ⟨u * u' + (m * n ^ 2) * (r * s' + s * r'),
            u * r' + r * u' + (m * n ^ 2) * s * s',
            u * s' + s * u' + r * r', ?_⟩
          push_cast at hroot ⊢
          linear_combination ((r : K) * s' + s * r' + (s : K) * s' * pb.gen) * hroot
      }
      have hle : adjoin ℤ ({pb.gen} : Set K) ≤ subalgebraOfSubring T := by
        apply adjoin_le
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        change pb.gen ∈ T
        exact ⟨0, 1, 0, by simp⟩
      exact hle hy
    have hbetaRel : pb.gen ^ 2 / (n : K) =
        (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
      have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      have hvSq : (v : K) ^ 2 = 1 := by
        rcases hv with hv | hv <;> rw [hv] <;> norm_num
      calc
        pb.gen ^ 2 / (n : K) =
            (v : K) ^ 2 * (pb.gen ^ 2 / (n : K)) := by rw [hvSq]; ring
        _ = (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
          dsimp [gamma]
          field_simp
          ring
    have hS_alphaSq : pb.gen ^ 2 ∈ S := by
      have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      refine ⟨-(n * v), -(n * v * c), 3 * n * v, ?_⟩
      calc
        pb.gen ^ 2 = (n : K) * (pb.gen ^ 2 / (n : K)) := by field_simp [hnK]
        _ = (-(n * v) : ℤ) + (-(n * v * c) : ℤ) * pb.gen +
            (3 * n * v : ℤ) * gamma := by
          rw [hbetaRel]
          push_cast
          ring
    have hadjoin {y : K} (hy : y ∈ adjoin ℤ ({pb.gen} : Set K)) : y ∈ S := by
      obtain ⟨u, r, s, rfl⟩ := hspan hy
      exact hS_add (hS_add ⟨u, 0, 0, by simp⟩
        (hS_smul r ⟨0, 1, 0, by simp⟩)) (hS_smul s hS_alphaSq)
    let N : ℕ := (27 * (m * n ^ 2) ^ 2).toNat
    have hNInt : (N : ℤ) = 27 * (m * n ^ 2) ^ 2 := by
      exact Int.toNat_of_nonneg (by positivity)
    have hNne : N ≠ 0 := by
      intro h
      have hzero : (27 : ℤ) * (m * n ^ 2) ^ 2 = 0 := by simpa [h] using hNInt.symm
      have hmn : m * n ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hn)
      nlinarith [sq_pos_of_ne_zero hmn]
    have hprimeCase (p : ℕ) (hp : p.Prime) (hpdvdN : p ∣ N) :
        p = 3 ∨
        (((p : ℤ) ∣ m * n ^ 2 ∧ ¬(p : ℤ) ^ 2 ∣ m * n ^ 2 ∧
            IsCoprime (p : ℤ) (3 * n)) ∨
          ((p : ℤ) ∣ m ^ 2 * n ∧ ¬(p : ℤ) ^ 2 ∣ m ^ 2 * n ∧
            IsCoprime (p : ℤ) (3 * m))) := by
      have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hpdiv : (p : ℤ) ∣ 27 * (m * n ^ 2) ^ 2 := by
        have hi : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpdvdN
        simpa [hNInt] using hi
      rcases hpI.dvd_mul.mp hpdiv with h27 | hd2
      · left
        have h27' : (p : ℤ) ∣ (3 : ℤ) ^ 3 := by simpa using h27
        have h3 : p ∣ 3 := by exact_mod_cast hpI.dvd_of_dvd_pow h27'
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3
      · right
        have hpd : (p : ℤ) ∣ m * n ^ 2 := hpI.dvd_of_dvd_pow hd2
        have hp3 : p ≠ 3 := by
          intro h
          subst p
          have hbad : (3 : ℤ) ∣ c ^ 3 * m * n ^ 2 := by
            change (3 : ℤ) ∣ m * n ^ 2 at hpd
            obtain ⟨w, hw⟩ := hpd
            refine ⟨c ^ 3 * w, ?_⟩
            calc
              c ^ 3 * m * n ^ 2 = c ^ 3 * (m * n ^ 2) := by ring
              _ = c ^ 3 * (3 * w) := by rw [hw]
              _ = 3 * (c ^ 3 * w) := by ring
          rw [hcubic] at hbad
          obtain ⟨e, he⟩ := hbad
          omega
        have hpge : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
        have hnotunit : ¬IsUnit (p : ℤ) := by
          intro hu
          simp only [Int.isUnit_iff] at hu
          omega
        have hnot3 : ¬(p : ℤ) ∣ 3 := by
          intro h
          have hnat : p ∣ 3 := by exact_mod_cast h
          exact hp3 ((Nat.prime_dvd_prime_iff_eq hp
            (by norm_num : Nat.Prime 3)).mp hnat)
        have hboth (hpm : (p : ℤ) ∣ m) (hpn : (p : ℤ) ∣ n) : False := by
          obtain ⟨e, f, hef⟩ := hcop
          have hpone : (p : ℤ) ∣ 1 := by
            rw [← hef]
            exact dvd_add (dvd_mul_of_dvd_right hpm _)
              (dvd_mul_of_dvd_right hpn _)
          exact hnotunit (isUnit_of_dvd_one hpone)
        have hpm_or_hpn : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n := by
          rcases hpI.dvd_mul.mp hpd with hpm | hpn2
          · exact Or.inl hpm
          · exact Or.inr (hpI.dvd_of_dvd_pow hpn2)
        rcases hpm_or_hpn with hpm | hpn
        · have hnotn : ¬(p : ℤ) ∣ n := fun hpn => hboth hpm hpn
          left
          refine ⟨hpd, ?_, ?_⟩
          · intro hsq
            have hnotn2 : ¬(p : ℤ) ∣ n ^ 2 := by
              intro h
              exact hnotn (hpI.dvd_of_dvd_pow h)
            have hpm2 : (p : ℤ) ^ 2 ∣ m :=
              hpI.pow_dvd_of_dvd_mul_right 2 hnotn2 hsq
            exact hnotunit (hmsq (p : ℤ) (by simpa [pow_two] using hpm2))
          · apply hpI.coprime_iff_not_dvd.mpr
            intro h
            rcases hpI.dvd_mul.mp h with h3 | hn
            · exact hnot3 h3
            · exact hnotn hn
        · have hnotm : ¬(p : ℤ) ∣ m := fun hpm => hboth hpm hpn
          right
          refine ⟨dvd_mul_of_dvd_right hpn _, ?_, ?_⟩
          · intro hsq
            have hnotm2 : ¬(p : ℤ) ∣ m ^ 2 := by
              intro h
              exact hnotm (hpI.dvd_of_dvd_pow h)
            have hpn2 : (p : ℤ) ^ 2 ∣ n :=
              hpI.pow_dvd_of_dvd_mul_left 2 hnotm2 hsq
            exact hnotunit (hnsq (p : ℤ) (by simpa [pow_two] using hpn2))
          · apply hpI.coprime_iff_not_dvd.mpr
            intro h
            rcases hpI.dvd_mul.mp h with h3 | hm
            · exact hnot3 h3
            · exact hnotm hm
    have hthree (z : K) (hzint : IsIntegral ℤ z)
        (h3z : ∃ u r s : ℤ,
          (3 : K) * z = (u : K) + (r : K) * pb.gen +
            (s : K) * ((1 + (c : K) * pb.gen +
              (v : K) * (pb.gen ^ 2 / (n : K))) / 3)) :
        ∃ u r s : ℤ,
          z = (u : K) + (r : K) * pb.gen +
            (s : K) * ((1 + (c : K) * pb.gen +
              (v : K) * (pb.gen ^ 2 / (n : K))) / 3) := by
      let theta : K := (c : K) * pb.gen
      let beta : K := pb.gen ^ 2 / (n : K)
      let gamma : K := (1 + (c : K) * pb.gen + (v : K) * beta) / 3
      let eta : K := (1 + theta + theta ^ 2) / 3
      let t : ℤ := c ^ 3 * n
      let S : Set K := {x | ∃ u r s : ℤ,
        x = (u : K) + (r : K) * pb.gen + (s : K) * gamma}
      let A : Set K := {x | ∃ u r s : ℤ,
        x = (u : K) + (r : K) * theta + (s : K) * eta}
      have hcnz : c ≠ 0 := by
        intro hc
        rw [hc] at hcubic
        norm_num at hcubic
        omega
      have hcK : (c : K) ≠ 0 := by exact_mod_cast hcnz
      have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      have hrootTheta : theta ^ 3 = ((1 + 9 * a : ℤ) : K) := by
        dsimp [theta]
        rw [mul_pow, hroot]
        have h := congrArg (fun x : ℤ => (x : K)) hcubic
        convert h using 1 <;> push_cast <;> ring
      have hthetaTop : adjoin ℚ ({theta} : Set K) = ⊤ := by
        apply PowerBasis.adjoin_eq_top_of_gen_mem_adjoin (B := pb)
        have ht : theta ∈ adjoin ℚ ({theta} : Set K) :=
          subset_adjoin (Set.mem_singleton _)
        have hscaled := Subalgebra.smul_mem (adjoin ℚ ({theta} : Set K)) ht (c : ℚ)⁻¹
        have heq : pb.gen = ((c : ℚ)⁻¹ : K) * theta := by
          dsimp [theta]
          push_cast
          field_simp [hcK]
        rw [heq]
        simpa [Algebra.smul_def] using hscaled
      have hthetaInt : IsIntegral ℚ theta := by
        apply IsIntegral.of_pow (n := 3) (by norm_num)
        rw [hrootTheta]
        exact isIntegral_intCast (1 + 9 * a)
      let pbTheta : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hthetaInt hthetaTop
      have hpbGen : pbTheta.gen = theta := by simp [pbTheta]
      have hpbDim : pbTheta.dim = 3 := by
        have hfin := pbTheta.finrank
        rw [pb.finrank, h3] at hfin
        exact hfin.symm
      have hvSq : (v : K) ^ 2 = 1 := by
        rcases hv with hv | hv <;> rw [hv] <;> norm_num
      have hbetaRel : beta = (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
        calc
          beta = (v : K) ^ 2 * beta := by rw [hvSq]; ring
          _ = (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
            dsimp [gamma]
            field_simp
            ring
      have hetaRel : eta = gamma + (k : K) * beta := by
        have hcvK : (c : K) ^ 2 * (n : K) = (v : K) + 3 * (k : K) := by
          exact_mod_cast hcv
        dsimp [eta, theta, gamma, beta]
        field_simp [hnK]
        linear_combination (pb.gen ^ 2) * hcvK
      have hS_add {x y : K} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by
        obtain ⟨u, r, s, rfl⟩ := hx
        obtain ⟨u', r', s', rfl⟩ := hy
        refine ⟨u + u', r + r', s + s', ?_⟩
        push_cast
        ring
      have hS_smul (d : ℤ) {x : K} (hx : x ∈ S) : (d : K) * x ∈ S := by
        obtain ⟨u, r, s, rfl⟩ := hx
        refine ⟨d * u, d * r, d * s, ?_⟩
        push_cast
        ring
      have hA_add {x y : K} (hx : x ∈ A) (hy : y ∈ A) : x + y ∈ A := by
        obtain ⟨u, r, s, rfl⟩ := hx
        obtain ⟨u', r', s', rfl⟩ := hy
        refine ⟨u + u', r + r', s + s', ?_⟩
        push_cast
        ring
      have hA_smul (d : ℤ) {x : K} (hx : x ∈ A) : (d : K) * x ∈ A := by
        obtain ⟨u, r, s, rfl⟩ := hx
        refine ⟨d * u, d * r, d * s, ?_⟩
        push_cast
        ring
      have hA_thetaSq : theta ^ 2 ∈ A := by
        refine ⟨-1, -1, 3, ?_⟩
        dsimp [eta]
        field_simp
        ring
      have hAinS {x : K} (hx : x ∈ A) : x ∈ S := by
        obtain ⟨u, r, s, rfl⟩ := hx
        have hbetaS : beta ∈ S := by
          refine ⟨-v, -(v * c), 3 * v, ?_⟩
          rw [hbetaRel]
          push_cast
          ring
        have hetaS : eta ∈ S := by
          rw [hetaRel]
          exact hS_add ⟨0, 0, 1, by simp⟩ (hS_smul k hbetaS)
        have hthetaS : theta ∈ S := by
          refine ⟨0, c, 0, ?_⟩
          simp [theta]
        exact hS_add (hS_add ⟨u, 0, 0, by simp⟩ (hS_smul r hthetaS))
          (hS_smul s hetaS)
      have htSinA {x : K} (hx : x ∈ S) : (t : K) * x ∈ A := by
        obtain ⟨u, r, s, rfl⟩ := hx
        have htbeta : (t : K) * beta = (c : K) * theta ^ 2 := by
          dsimp [t, beta, theta]
          field_simp [hnK]
          push_cast
          ring
        have htalpha : (t : K) * pb.gen = ((c ^ 2 * n : ℤ) : K) * theta := by
          dsimp [t, theta]
          push_cast
          ring
        have htgamma : (t : K) * gamma =
            (t : K) * eta - ((k * c : ℤ) : K) * theta ^ 2 := by
          calc
            (t : K) * gamma = (t : K) * eta - (k : K) * ((t : K) * beta) := by
              rw [hetaRel]
              ring
            _ = (t : K) * eta - ((k * c : ℤ) : K) * theta ^ 2 := by
              rw [htbeta]
              push_cast
              ring
        have htalphaA : (t : K) * pb.gen ∈ A := by
          rw [htalpha]
          exact hA_smul (c ^ 2 * n) ⟨0, 1, 0, by simp⟩
        have htgammaA : (t : K) * gamma ∈ A := by
          rw [htgamma]
          have hetaA : eta ∈ A := ⟨0, 0, 1, by simp⟩
          convert hA_add (hA_smul t hetaA)
            (hA_smul (-(k * c)) hA_thetaSq) using 1 <;> push_cast <;> ring
        have htuA : ((t * u : ℤ) : K) ∈ A := ⟨t * u, 0, 0, by simp⟩
        have hsum := hA_add (hA_add
          htuA (hA_smul r htalphaA))
          (hA_smul s htgammaA)
        convert hsum using 1 <;> push_cast <;> ring
      have ht3 : ¬(3 : ℤ) ∣ t := by
        intro ht
        have hd : (3 : ℤ) ∣ c ^ 3 * m * n ^ 2 := by
          have h := dvd_mul_of_dvd_left ht (m * n)
          change (3 : ℤ) ∣ (c ^ 3 * n) * (m * n) at h
          convert h using 1 <;> ring
        rw [hcubic] at hd
        obtain ⟨e, he⟩ := hd
        omega
      have hcop : IsCoprime (3 : ℤ) t :=
        (show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mpr ht3
      have h3zS : (3 : K) * z ∈ S := h3z
      have h3tzA : (3 : K) * ((t : K) * z) ∈ A := by
        convert htSinA h3zS using 1 <;> ring
      have htzint : IsIntegral ℤ ((t : K) * z) :=
        (isIntegral_algebraMap : IsIntegral ℤ (t : K)).mul hzint
      have htzA : (t : K) * z ∈ A := by
        change ∃ u r s : ℤ, (t : K) * z = (u : K) + (r : K) * theta + (s : K) * eta
        change ∃ u r s : ℤ, (3 : K) * ((t : K) * z) =
          (u : K) + (r : K) * theta + (s : K) * eta at h3tzA
        exact D5.S3.Arith.Lattices.PureCubicThreeSaturation.pure_cubic_three_saturation
          pbTheta hpbDim a (by simpa [hpbGen] using hrootTheta)
          ((t : K) * z) htzint (by simpa only [hpbGen, eta] using h3tzA)
      obtain ⟨e, f, hef⟩ := hcop
      have hzS := hS_add (hS_smul e h3zS) (hS_smul f (hAinS htzA))
      have heq : z = (e : K) * ((3 : K) * z) + (f : K) * ((t : K) * z) := by
        have hcoef : (e : K) * 3 + (f : K) * (t : K) = 1 := by exact_mod_cast hef
        calc
          z = ((e : K) * 3 + (f : K) * (t : K)) * z := by rw [hcoef, one_mul]
          _ = _ := by ring
      rw [← heq] at hzS
      exact hzS
    have hremove : ∀ q : ℕ, q ∣ N → ∀ y : K,
        IsIntegral ℤ y → (q : K) * y ∈ S → y ∈ S := by
      intro q
      induction q using Nat.strong_induction_on with
      | h q ih =>
        intro hqN y hyint hqy
        by_cases hq1 : q = 1
        · simpa [hq1] using hqy
        have hq0 : q ≠ 0 := by
          intro h
          apply hNne
          simpa [h] using hqN
        obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
        obtain ⟨q', hq'⟩ := hpq
        have hq'0 : q' ≠ 0 := by
          intro h
          apply hq0
          simpa [h] using hq'
        have hq'lt : q' < q := by
          calc
            q' = 1 * q' := by simp
            _ < p * q' := Nat.mul_lt_mul_of_pos_right hp.one_lt
              (Nat.pos_of_ne_zero hq'0)
            _ = q := hq'.symm
        have hq'N : q' ∣ N :=
          dvd_trans ⟨p, by simpa [mul_comm] using hq'⟩ hqN
        have hpN : p ∣ N := dvd_trans ⟨q', hq'⟩ hqN
        have hq'yint : IsIntegral ℤ ((q' : K) * y) :=
          (show IsIntegral ℤ (q' : K) from by
            simpa using (isIntegral_algebraMap : IsIntegral ℤ (((q' : ℤ) : K)))).mul hyint
        have hpq'y : (p : K) * ((q' : K) * y) ∈ S := by
          convert hqy using 1
          rw [hq']
          push_cast
          ring
        have hq'y : (q' : K) * y ∈ S := by
          rcases hprimeCase p hp hpN with hp3 | hlocal
          · subst p
            exact hthree _ hq'yint hpq'y
          · exact D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation.pure_cubic_mixed_prime_saturation
                pb h3 m n c a k v hm hn hv hroot hcubic hcv
                p hp hlocal _ hq'yint hpq'y
        exact ih q' hq'lt hq'N y hyint hq'y
    intro z hzint
    have hcleared := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hAlphaInt hzint
    have hclearedS : ((-27 * (m * n ^ 2) ^ 2 : ℤ) : K) * z ∈ S := by
      apply hadjoin
      have heq : ((-27 * (m * n ^ 2) ^ 2 : ℤ) : K) * z =
          Algebra.discr ℚ pb.basis • z := by
        rw [hdisc]
        simp [Algebra.smul_def, map_mul, map_pow]
      rw [heq]
      exact hcleared
    have hNz : (N : K) * z ∈ S := by
      have h := hS_smul (-1) hclearedS
      have hNK : (N : K) = ((27 * (m * n ^ 2) ^ 2 : ℤ) : K) := by
        exact_mod_cast hNInt
      convert h using 1
      rw [hNK]
      push_cast
      ring
    exact hremove N dvd_rfl z hzint hNz

  have hdiscField : NumberField.discr K = -3 * (m * n) ^ 2 := by
    classical
    obtain ⟨hAlpha, _, hGamma, _, b2, _, hb2, _, hdisc2⟩ :=
      D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices
        pb h3 m n c a k v hm hn hv hroot hcubic hcv
    have hb20 : b2 0 = (1 : K) := by
      have h := congrFun hb2 0
      simpa using h
    have hb21 : b2 1 = pb.gen := by
      have h := congrFun hb2 1
      simpa using h
    have hb22 : b2 2 =
        (1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3 := by
      have h := congrFun hb2 2
      simpa using h
    have hb2int (i : Fin 3) : IsIntegral ℤ (b2 i) := by
      fin_cases i
      · change IsIntegral ℤ (b2 0)
        rw [hb20]
        exact isIntegral_one
      · change IsIntegral ℤ (b2 1)
        rw [hb21]
        exact hAlpha
      · change IsIntegral ℤ (b2 2)
        rw [hb22]
        exact hGamma
    have hrepr (z : K) (hzint : IsIntegral ℤ z) (i : Fin 3) :
        IsIntegral ℤ (b2.repr z i) := by
      obtain ⟨u, r, s, hz⟩ := hmax z hzint
      have hcoord : z = (u : ℚ) • b2 0 + (r : ℚ) • b2 1 + (s : ℚ) • b2 2 := by
        rw [hb20, hb21, hb22]
        simpa [Algebra.smul_def] using hz
      rw [hcoord]
      fin_cases i <;>
        simp [map_add, map_smul, Basis.repr_self] <;>
        exact isIntegral_algebraMap
    have hto1 : ∀ i j, IsIntegral ℤ
        (b2.toMatrix (NumberField.integralBasis K) i j) := by
      intro i j
      rw [Basis.toMatrix_apply]
      exact hrepr _ (by
        rw [NumberField.integralBasis_apply]
        exact NumberField.RingOfIntegers.isIntegral_coe _) i
    have hto2 : ∀ i j, IsIntegral ℤ
        ((NumberField.integralBasis K).toMatrix b2 i j) := by
      intro i j
      rw [Basis.toMatrix_apply]
      let x : 𝓞 K := ⟨b2 j, hb2int j⟩
      change IsIntegral ℤ
        ((NumberField.integralBasis K).repr
          (algebraMap (𝓞 K) K x) i)
      rw [NumberField.integralBasis_repr_apply]
      exact isIntegral_algebraMap
    have hdiscEq : Algebra.discr ℚ b2 =
        Algebra.discr ℚ (NumberField.integralBasis K) :=
      Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral K hto1 hto2
    have hrat : (NumberField.discr K : ℚ) =
        -3 * (((m * n : ℤ) : ℚ)) ^ 2 := by
      rw [NumberField.coe_discr, ← hdiscEq, hdisc2]
    exact_mod_cast hrat
  have hfull (z : K) : IsIntegral ℤ z ↔ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3) := by
    constructor
    · exact hmax z
    · rintro ⟨u, r, s, rfl⟩
      obtain ⟨hAlpha, _, hGamma, _, _, _, _, _, _⟩ :=
        D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices
          pb h3 m n c a k v hm hn hv hroot hcubic hcv
      exact (isIntegral_algebraMap.add (isIntegral_algebraMap.mul hAlpha)).add
        (isIntegral_algebraMap.mul hGamma)
  exact ⟨hfull, hdiscField⟩

#print axioms pure_cubic_mixed_maximality_and_discriminant

end D5.S3.Arith.Lattices.PureCubicMixedMaximality
