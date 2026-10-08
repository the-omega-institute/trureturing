/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier annihilators define a projection with an exact Clifford average. -/
/-
proof_shape: fourierVacuum_properties: content
escape_witness: fourierVacuum_properties
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.fourier
  declaration statement_id: sha256:0706c337d65e033c10b3e874026fbc51bf5811becfd9777ca8892400ea826c21
Supporting lane modules are first-freeze dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: twirl_cross_antisymmetric: bind-only; consumer: twirl_real_unit_invariance
proof_shape: twirl_real_unit_invariance: bind-only; consumer: modeUnit_twirl
proof_shape: CAR_nilpotent: bind-only; consumer: modeUnit_square
proof_shape: CAR_projector_square: bind-only; consumer: CAR_flip_projector
proof_shape: CAR_projectors_commute: bind-only; consumer: numberProjections_commute
proof_shape: conjugations_commute: bind-only; consumer: finiteTwirl_invariant
proof_shape: finiteTwirl_step: bind-only; consumer: finiteTwirl_invariant
proof_shape: finiteTwirl_invariant: content; consumer: cliffordAverage_invariant
proof_shape: finiteTwirl_one: content; consumer: cliffordAverage_one
proof_shape: twirl_projection_halving: bind-only; consumer: vacuum_twirl_normalization
proof_shape: CAR_flip_projector: bind-only; consumer: modeUnit_flip
proof_shape: vacuumWord_step: bind-only; consumer: vacuumWord_fixed
proof_shape: vacuumWord_fixed: content; consumer: vacuum_twirl_normalization
proof_shape: vacuum_twirl_normalization: content; consumer: fourierVacuum_properties
proof_shape: twirl_generator_cyclic: bind-only; consumer: twirl_linear_cyclic
proof_shape: twirl_linear_cyclic: bind-only; consumer: fourierVacuum_contractions
proof_shape: vacuum_pair_contractions: bind-only; consumer: fourierVacuum_contractions
proof_shape: vacuumWord_commutes: bind-only; consumer: vacuumWord_projection
proof_shape: vacuumWord_projection: content; consumer: vacuumWord_psd
proof_shape: vacuumWord_annihilate: content; consumer: fourierVacuum_properties
proof_shape: anticommute_commutes_number: bind-only; consumer: numberProjection_commute_mode
proof_shape: vacuumWord_psd: bind-only; consumer: fourierVacuum_psd
proof_shape: cliffordLinear_anticommutator: bind-only; consumer: fourierMode_CAR
proof_shape: cliffordLinear_star: bind-only; consumer: fourierMode_CAR
proof_shape: modeScale_star: bind-only; consumer: modeCoeff_inner
proof_shape: modeScale_square: bind-only; consumer: modeCoeff_inner
proof_shape: phase_fin_orthogonality: bind-only; consumer: modeCoeff_inner
proof_shape: modeCoeff_inner: bind-only; consumer: fourierMode_CAR
proof_shape: modeCoeff_literal: bind-only; consumers: modeCoeff_inner, modeCoeff_bilinear, modeCoeff_complete, CliffordBondParents.modeCoeff_bond, CliffordBondParents.modeCoeff_closing
proof_shape: modeCoeff_bilinear: bind-only; consumer: fourierMode_CAR
proof_shape: fourierMode_CAR: bind-only; consumer: totalMode_CAR
proof_shape: modeCoeff_unit_square: bind-only; consumer: modeUnit_twirl
proof_shape: cliffordAverage_invariant: bind-only; consumer: modeUnit_twirl
proof_shape: cliffordAverage_one: bind-only; consumer: fourierVacuum_properties
proof_shape: modeUnit_twirl: bind-only; consumer: fourierVacuum_properties
proof_shape: totalMode_CAR: bind-only; consumer: modeUnit_square
proof_shape: numberProjection_star: bind-only; consumer: modeUnit_fix
proof_shape: modeUnit_square: bind-only; consumer: modeUnit_fix
proof_shape: numberProjection_commute_mode: bind-only; consumer: modeUnit_fix
proof_shape: numberProjection_square: bind-only; consumer: fourierVacuum_properties
proof_shape: numberProjections_commute: bind-only; consumer: fourierVacuum_properties
proof_shape: modeUnit_flip: bind-only; consumer: fourierVacuum_properties
proof_shape: modeUnit_fix: bind-only; consumer: fourierVacuum_properties
proof_shape: fourierVacuum_psd: bind-only; consumer: uniform_majorana_parent
proof_shape: cycle_cosine_completeness: bind-only; consumer: modeCoeff_complete
proof_shape: modeCoeff_complete: bind-only; consumer: fourierMode_reconstruct
proof_shape: fourierMode_reconstruct: bind-only; consumer: fourierVacuum_covariance
proof_shape: fourierVacuum_contractions: bind-only; consumer: fourierVacuum_covariance
proof_shape: fourierVacuum_covariance: content; consumer: uniform_majorana_parent
-/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma twirl_cross_antisymmetric (g : ι → R)
    (hsq : ∀ j, g j * g j = 1)
    (hanti : ∀ j k, j ≠ k → g j * g k = -(g k * g j))
    (T : R →ₗ[ℂ] R) (hT : ∀ j X, T (g j * X * g j) = T X)
    (j k : ι) (hjk : j ≠ k) (X : R) :
    T (g j * X * g k) = -T (g k * X * g j) := by
  have hfirst : T (g j * X * g k) = T (X * (g k * g j)) := by
    have h := hT j (X * (g k * g j))
    simpa only [← mul_assoc, mul_assoc (g j * X * g k), hsq j, mul_one] using h
  have hsecond : T (g k * X * g j) = T (X * (g j * g k)) := by
    have h := hT k (X * (g j * g k))
    simpa only [← mul_assoc, mul_assoc (g k * X * g j), hsq k, mul_one] using h
  rw [hfirst, hsecond, hanti k j hjk.symm, mul_neg, map_neg]
private lemma twirl_real_unit_invariance (g : ι → R)
    (hsq : ∀ j, g j * g j = 1)
    (hanti : ∀ j k, j ≠ k → g j * g k = -(g k * g j))
    (T : R →ₗ[ℂ] R) (hT : ∀ j X, T (g j * X * g j) = T X)
    (c : ι → ℂ) (hc : ∑ j, c j * c j = 1) (X : R) :
    T ((∑ j, c j • g j) * X * (∑ j, c j • g j)) = T X := by
  classical
  let f : ι → ι → R := fun j k => (c j * c k) • T (g j * X * g k)
  have hf : ∀ j k, f j k + f k j =
      if j = k then (2 * (c j * c j)) • T X else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst k
      simp only [f, hT, ↓reduceIte]
      module
    · simp only [f, hjk, ↓reduceIte]
      rw [twirl_cross_antisymmetric g hsq hanti T hT j k hjk X, mul_comm (c k) (c j)]
      simp
  have hdouble : (∑ j, ∑ k, f j k) + (∑ j, ∑ k, f j k) = (2 : ℂ) • T X := by
    calc
      (∑ j, ∑ k, f j k) + (∑ j, ∑ k, f j k) =
        (∑ j, ∑ k, f j k) + (∑ j, ∑ k, f k j) := by rw [Finset.sum_comm (f := f)]
      _ = ∑ j, ∑ k, (f j k + f k j) := by simp [Finset.sum_add_distrib]
      _ = ∑ j, (2 * (c j * c j)) • T X := by simp_rw [hf]; simp
      _ = (2 : ℂ) • T X := by
        rw [← Finset.sum_smul, ← Finset.mul_sum, hc, mul_one]
  have hexp : T ((∑ j, c j • g j) * X * (∑ j, c j • g j)) = ∑ j, ∑ k, f j k := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      map_sum, map_smul, Finset.smul_sum, f]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm]
  rw [hexp]
  calc
    (∑ j, ∑ k, f j k) = (1 / 2 : ℂ) • ((∑ j, ∑ k, f j k) + (∑ j, ∑ k, f j k)) := by module
    _ = T X := by rw [hdouble, smul_smul]; norm_num
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
private lemma CAR_nilpotent (b : R) (hbb : b * b + b * b = 0) : b * b = 0 := by
  have hhalf := congrArg (fun X : R => (1 / 2 : ℂ) • X) hbb
  calc
    b * b = (1 / 2 : ℂ) • (b * b + b * b) := by module
    _ = 0 := by rw [hbb, smul_zero]
private lemma CAR_projector_square (b : R) (hbb : b * b = 0)
    (hCAR : b * star b + star b * b = 1) :
    (b * star b) * (b * star b) = b * star b := by
  have hstar : star b * star b = 0 := by
    have h := congrArg star hbb
    simpa only [star_mul, star_zero] using h
  calc
    (b * star b) * (b * star b) = b * (star b * b) * star b := by noncomm_ring
    _ = b * (1 - b * star b) * star b := by rw [← hCAR]; noncomm_ring
    _ = b * star b := by
      simp only [mul_sub, sub_mul, mul_one]
      have hz : b * (b * star b) * star b = 0 := by
        rw [← mul_assoc b b (star b), hbb, zero_mul, zero_mul]
      rw [hz, sub_zero]
private lemma anticommute_commutes_number (b c : R)
    (hbc : b*c=-(c*b)) (hbcs : b*star c=-(star c*b)) :
    b*(c*star c)=(c*star c)*b := by
  rw [← mul_assoc, hbc, neg_mul, mul_assoc, hbcs, mul_neg, neg_neg, ← mul_assoc]
private lemma CAR_projectors_commute (b c : R)
    (hbc : b * c = -(c * b)) (hbcstar : b * star c = -(star c * b)) :
    (b * star b) * (c * star c) = (c * star c) * (b * star b) := by
  have hb := anticommute_commutes_number b c hbc hbcstar
  have hs := anticommute_commutes_number (star b) c
    (by simpa only [star_mul, star_star, star_neg, neg_neg] using congrArg Neg.neg (congrArg star hbcstar).symm)
    (by simpa only [star_mul, star_star, star_neg, neg_neg] using congrArg Neg.neg (congrArg star hbc).symm)
  calc
    (b * star b) * (c * star c) = b * ((c * star c) * star b) := by
      rw [mul_assoc, hs]
    _ = (c * star c) * (b * star b) := by rw [← mul_assoc, hb, mul_assoc]

end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
private lemma conjugations_commute (u v : R) (huv : u*v=-(v*u)) :
    ((LinearMap.mulLeftRight ℂ (u, u))).comp ((LinearMap.mulLeftRight ℂ (v, v))) = ((LinearMap.mulLeftRight ℂ (v, v))).comp ((LinearMap.mulLeftRight ℂ (u, u))) := by
  ext X
  change u * (v*X*v)*u = v*(u*X*u)*v
  calc
    u * (v*X*v)*u = (u*v)*X*(v*u) := by simp only [mul_assoc]
    _ = (v*u)*X*(u*v) := by rw [huv]; simp
    _ = v*(u*X*u)*v := by simp only [mul_assoc]
def averaging (u : R) : R →ₗ[ℂ] R := (1/2 : ℂ) • (LinearMap.id + (LinearMap.mulLeftRight ℂ (u, u)))
def finiteTwirl (g : ℕ → R) (k : ℕ) : R →ₗ[ℂ] R :=
  ((List.range k).map (fun j => averaging (g j))).prod
lemma finiteTwirl_step (g : ℕ → R) (k : ℕ) (X : R) :
    finiteTwirl g (k+1) X = (1/2 : ℂ) •
      (finiteTwirl g k X + finiteTwirl g k (g k * X * g k)) := by
  simp [finiteTwirl, List.prod_range_succ, Module.End.mul_apply, averaging,
    LinearMap.mulLeftRight_apply, map_smul, map_add]
private lemma finiteTwirl_invariant (g : ℕ → R) (m : ℕ)
    (hsq : ∀ j, j < m → g j*g j=1)
    (hanti : ∀ k j, k < m → j < m → k ≠ j → g k*g j=-(g j*g k)) :
    ∀ j, j < m → ∀ X, finiteTwirl g m (g j*X*g j) = finiteTwirl g m X := by
  induction m with
  | zero => intros; omega
  | succ m ih =>
    intro j hj X
    by_cases hjm : j = m
    · subst j
      rw [finiteTwirl_step, finiteTwirl_step]
      have hc : g m * (g m*X*g m) * g m = X := by
        calc
          _ = (g m*g m)*X*(g m*g m) := by simp only [mul_assoc]
          _ = X := by rw [hsq m (by omega), one_mul, mul_one]
      rw [hc, add_comm]
    · have hj' : j < m := by omega
      have hi := ih (fun k hk => hsq k (by omega))
        (fun k l hk hl hkl => hanti k l (by omega) (by omega) hkl) j hj'
      have hc := conjugations_commute (g m) (g j) (hanti m j (by omega) hj (Ne.symm hjm))
      have hx := LinearMap.congr_fun hc X
      change g m*(g j*X*g j)*g m = g j*(g m*X*g m)*g j at hx
      rw [finiteTwirl_step, finiteTwirl_step, hi, hx, hi]
private lemma finiteTwirl_one (g : ℕ → R) (m : ℕ) (hsq : ∀ j, j < m → g j*g j=1) :
    finiteTwirl g m 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [finiteTwirl_step, mul_one, hsq m (by omega), ih (fun k hk => hsq k (by omega))]
    module
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
private lemma twirl_projection_halving (T : R →ₗ[ℂ] R) (p q u : R)
    (hu2 : u * u = 1) (hT : ∀ X, T (u * X * u) = T X)
    (hflip : u * p * u = 1 - p) (hq : u * q * u = q) :
    T (p * q) = (1 / 2 : ℂ) • T q := by
  have hconj : u * (p * q) * u = (1 - p) * q := by
    calc
      u * (p * q) * u = (u * p * u) * (u * q * u) := by
        symm
        calc
          _ = u * p * (u * u) * q * u := by simp only [mul_assoc]
          _ = _ := by rw [hu2]; simp only [mul_one, mul_assoc]
      _ = (1-p)*q := by rw [hflip, hq]
  have heq : T (p * q) = T q - T (p * q) := by
    calc
      T (p*q) = T (u * (p*q) * u) := (hT (p*q)).symm
      _ = T q - T (p*q) := by rw [hconj, sub_mul, one_mul, map_sub]
  calc
    T (p*q) = (1 / 2 : ℂ) • (T (p*q) + T (p*q)) := by module
    _ = (1 / 2 : ℂ) • T q := by congr 1; exact (eq_sub_iff_add_eq.mp heq)
variable [StarRing R] [StarModule ℂ R]
private lemma CAR_flip_projector (b : R) (hbb : b * b = 0)
    (hCAR : b * star b + star b * b = 1) :
    (b + star b) * (b * star b) * (b + star b) = 1 - b * star b := by
  have hss : star b * star b = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hbb
  have hp := CAR_projector_square b hbb hCAR
  have hp' : (star b * b) * (star b * b) = star b * b :=
    by simpa only [star_star] using CAR_projector_square (star b) hss (by simpa [add_comm] using hCAR)
  calc
    (b + star b) * (b * star b) * (b + star b) =
        (star b * b) * (star b * b) := by
      have h1 : b * (b * star b) = 0 := by rw [← mul_assoc, hbb, zero_mul]
      have h2 : star b * (b * star b) * star b = 0 := by
        rw [mul_assoc, mul_assoc, hss, mul_zero, mul_zero]
      simp only [add_mul, mul_add, h1, zero_mul, zero_add, h2, add_zero]
      noncomm_ring
    _ = star b * b := hp'
    _ = 1 - b * star b := by rw [← hCAR]; noncomm_ring
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
def vacuumWord (p : ℕ → R) (k : ℕ) : R :=
  (((List.range k).reverse).map p).prod
private lemma vacuumWord_step (p : ℕ → R) (k : ℕ) :
    vacuumWord p (k+1) = p k * vacuumWord p k := by
  simp only [vacuumWord, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.prod_cons]
private lemma vacuumWord_fixed (p : ℕ → R) (u : R) (m : ℕ) (hu : u*u=1)
    (hp : ∀ k, k < m → u*p k*u=p k) : u*vacuumWord p m*u=vacuumWord p m := by
  induction m with
  | zero => simpa [vacuumWord] using hu
  | succ m ih =>
    have hm := hp m (by omega)
    have hi := ih (fun k hk => hp k (by omega))
    rw [vacuumWord_step]
    calc
      u*(p m*vacuumWord p m)*u = (u*p m*u)*(u*vacuumWord p m*u) := by
        symm
        calc
          _ = u*p m*(u*u)*vacuumWord p m*u := by simp only [mul_assoc]
          _ = _ := by rw [hu]; simp only [mul_one, mul_assoc]
      _ = _ := by rw [hm, hi]
private lemma vacuum_twirl_normalization (T : R →ₗ[ℂ] R) (p u : ℕ → R) (m : ℕ)
    (hu : ∀ k, k < m → u k*u k=1)
    (hT : ∀ k, k < m → ∀ X, T (u k*X*u k)=T X)
    (hflip : ∀ k, k < m → u k*p k*u k=1-p k)
    (hfix : ∀ k j, k < m → j < k → u k*p j*u k=p j) :
    T (vacuumWord p m) = ((1/2 : ℂ)^m) • T 1 := by
  induction m with
  | zero => simp [vacuumWord]
  | succ m ih =>
    have hi := ih (fun k hk => hu k (by omega)) (fun k hk => hT k (by omega))
      (fun k hk => hflip k (by omega)) (fun k j hk hj => hfix k j (by omega) hj)
    rw [vacuumWord_step, twirl_projection_halving T (p m) (vacuumWord p m) (u m)
      (hu m (by omega)) (hT m (by omega)) (hflip m (by omega))
      (vacuumWord_fixed p (u m) m (hu m (by omega))
        (fun k hk => hfix m k (by omega) hk)), hi, smul_smul]
    rw [pow_succ, mul_comm]
private lemma twirl_generator_cyclic {ι : Type*} (g : ι → R)
    (hsq : ∀ j, g j*g j=1) (T : R →ₗ[ℂ] R)
    (hT : ∀ j X, T (g j*X*g j)=T X) (j : ι) (X : R) :
    T (g j*X)=T (X*g j) := by
  have h := hT j (X*g j)
  simpa only [← mul_assoc, mul_assoc (g j*X), hsq, mul_one] using h
private lemma twirl_linear_cyclic {ι : Type*} [Fintype ι] (g : ι → R)
    (hsq : ∀ j, g j*g j=1) (T : R →ₗ[ℂ] R)
    (hT : ∀ j X, T (g j*X*g j)=T X) (c : ι → ℂ) (X : R) :
    T ((∑ j, c j • g j)*X)=T (X*(∑ j, c j • g j)) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [twirl_generator_cyclic g hsq T hT j X]
section Star
variable [StarRing R] [StarModule ℂ R]
private lemma vacuum_pair_contractions (T : R →ₗ[ℂ] R) (b c P : R) (δ : ℂ)
    (hb : b*P=0) (hc : c*P=0) (hbc : b*star c + star c*b=δ • (1:R))
    (hcycle : ∀ X, T (star b*X)=T (X*star b))
    (hPb : P*star b=0) :
    T (b*c*P)=0 ∧ T (star b*c*P)=0 ∧
      T (b*star c*P)=δ • T P ∧ T (star b*star c*P)=0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, hc, mul_zero, map_zero]
  · rw [mul_assoc, hc, mul_zero, map_zero]
  · have hz : star c*b*P=0 := by rw [mul_assoc, hb, mul_zero]
    have he : b*star c*P=δ • P := by
      calc
        _ = (b*star c + star c*b)*P := by rw [add_mul, hz, add_zero]
        _ = δ • P := by rw [hbc, smul_mul_assoc, one_mul]
    rw [he, map_smul]
  · rw [mul_assoc, hcycle, mul_assoc (star c), hPb, mul_zero, map_zero]
end Star
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
private lemma vacuumWord_commutes (p : ℕ → R) (q : R) (m : ℕ)
    (h : ∀ j, j < m → q*p j=p j*q) : q*vacuumWord p m=vacuumWord p m*q := by
  apply (Commute.list_prod_right (((List.range m).reverse).map p) q ?_).eq
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact h j (List.mem_range.mp (List.mem_reverse.mp hj))
private lemma vacuumWord_projection (p : ℕ → R) (m : ℕ)
    (hs : ∀ j, j < m → star (p j)=p j)
    (h2 : ∀ j, j < m → p j*p j=p j)
    (hcomm : ∀ j k, j < m → k < m → p j*p k=p k*p j) :
    star (vacuumWord p m)=vacuumWord p m ∧ vacuumWord p m*vacuumWord p m=vacuumWord p m := by
  induction m with
  | zero => simp [vacuumWord]
  | succ m ih =>
    have hi := ih (fun j hj => hs j (by omega)) (fun j hj => h2 j (by omega))
      (fun j k hj hk => hcomm j k (by omega) (by omega))
    have hc := vacuumWord_commutes p (p m) m (fun j hj => hcomm m j (by omega) (by omega))
    constructor
    · rw [vacuumWord_step, star_mul, hi.1, hs m (by omega), ← hc]
    · rw [vacuumWord_step]
      calc
        (p m*vacuumWord p m)*(p m*vacuumWord p m) =
          p m*(vacuumWord p m*p m)*vacuumWord p m := by simp only [mul_assoc]
        _ = (p m*p m)*(vacuumWord p m*vacuumWord p m) := by rw [← hc]; simp only [mul_assoc]
        _ = p m*vacuumWord p m := by rw [h2 m (by omega), hi.2]
private lemma vacuumWord_annihilate (p : ℕ → R) (b : R) (m r : ℕ) (hr : r < m)
    (hz : b*p r=0) (hcomm : ∀ j, j < m → j ≠ r → b*p j=p j*b) : b*vacuumWord p m=0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [vacuumWord_step, ← mul_assoc]
    by_cases he : m=r
    · subst m; rw [hz, zero_mul]
    · rw [hcomm m (by omega) he, mul_assoc, ih (by omega) (fun j hj hjr => hcomm j (by omega) hjr), mul_zero]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped ComplexOrder
private lemma vacuumWord_psd (p : ℕ → Matrix ι ι ℂ) (m : ℕ)
    (hs : ∀ j, j < m → star (p j)=p j)
    (h2 : ∀ j, j < m → p j*p j=p j)
    (hcomm : ∀ j k, j < m → k < m → p j*p k=p k*p j) :
    (vacuumWord p m).PosSemidef := by
  have hp := vacuumWord_projection p m hs h2 hcomm
  have he : vacuumWord p m=vacuumWord p m*(vacuumWord p m).conjTranspose := by
    rw [← Matrix.star_eq_conjTranspose, hp.1, hp.2]
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma cliffordLinear_anticommutator (g : ι → R)
    (hsq : ∀ j, g j*g j=1) (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j))
    (c d : ι → ℂ) :
    Fintype.linearCombination ℂ g c*Fintype.linearCombination ℂ g d+Fintype.linearCombination ℂ g d*Fintype.linearCombination ℂ g c =
      (2*∑ j, c j*d j) • (1:R) := by
  classical
  have he : Fintype.linearCombination ℂ g c * Fintype.linearCombination ℂ g d +
      Fintype.linearCombination ℂ g d * Fintype.linearCombination ℂ g c =
      ∑ j, ∑ k, (c j * d k + d j * c k) • (g j * g k) := by
    simp only [Fintype.linearCombination_apply, Finset.sum_mul_sum, smul_mul_smul,
      add_smul, Finset.sum_add_distrib]
  rw [he]
  have hsym := D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations.majorana_quadratic_symmetrization g hsq hanti
    (fun j k => c j * d k + d j * c k)
  have hskew (j k : ι) :
      (c j * d k + d j * c k) - (c k * d j + d k * c j) = 0 := by ring
  simp_rw [hskew, zero_smul] at hsym
  simp only [Finset.sum_const_zero, smul_zero, add_zero] at hsym
  rw [hsym, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

section Star
variable [StarRing R] [StarModule ℂ R]
private lemma cliffordLinear_star (g : ι → R) (hg : ∀ j, star (g j)=g j) (c : ι → ℂ) :
    star (Fintype.linearCombination ℂ g c)=Fintype.linearCombination ℂ g (fun j => star (c j)) := by
  simp [Fintype.linearCombination_apply, star_sum, star_smul, hg]
end Star
end
noncomputable section
def cycleFrequency (L : ℕ) (r : Fin L) : ℝ := (2*(r:ℝ)+1)*theta L
def modeScale (L : ℕ) : ℂ := ((Real.sqrt ((4*L:ℕ):ℝ))⁻¹:ℝ)
def modeCoeff (L : ℕ) (r : Fin L) (j : Fin (2*L)) : ℂ :=
  (Matrix.diagonal (fun k : Fin (2*L) =>
    modeScale L * (Real.sqrt ((2*L:ℕ):ℝ) : ℂ) *
      Complex.exp (((-(k:ℝ) * theta L : ℝ) : ℂ) * Complex.I)) *
    D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.fourier (2*L)) j
      (Fin.castLE (by omega) r)
private lemma modeCoeff_literal (L : ℕ) (r : Fin L) (j : Fin (2*L)) :
    modeCoeff L r j =
      modeScale L*(fun x : ℝ => (Real.probChar x : ℂ)) (-(j:ℝ)*cycleFrequency L r) := by
  have hL : 0 < L := by have := r.isLt; omega
  unfold modeCoeff
  rw [Matrix.diagonal_mul]
  simp only [D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.fourier, Fin.val_castLE,
    cycleFrequency, Real.probChar_apply, theta]
  have hs : (Real.sqrt ((2*L:ℕ):ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ) < (2*L:ℕ))
  rw [show modeScale L * (Real.sqrt ((2*L:ℕ):ℝ) : ℂ) *
      Complex.exp (((-(j:ℝ) * (Real.pi/(2*(L:ℝ))) : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (-((2:ℕ)*Real.pi*Complex.I*(j:ℕ)*(r:ℕ))/(2*L:ℕ)) / Real.sqrt (2*L:ℕ)) =
      modeScale L * (Complex.exp (((-(j:ℝ) * (Real.pi/(2*(L:ℝ))) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((2:ℕ)*Real.pi*Complex.I*(j:ℕ)*(r:ℕ))/(2*L:ℕ))) by field_simp]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  have hc : (L : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  field_simp
  ring
attribute [eqns modeCoeff_literal] modeCoeff
lemma modeScale_star (L : ℕ) : star (modeScale L)=modeScale L := by simp [modeScale]
lemma modeScale_square {L : ℕ} (hL : 0 < L) :
    modeScale L*modeScale L=((4*L:ℕ):ℂ)⁻¹ := by
  unfold modeScale
  rw [← Complex.ofReal_mul, ← mul_inv, ← sq, Real.sq_sqrt (by positivity)]
  simp
private lemma phase_fin_orthogonality {M : ℕ} (hM : 0 < M) (r s : Fin M) :
    (∑ j : Fin M, (fun x : ℝ => (Real.probChar x : ℂ)) ((2*Real.pi*((r:ℝ)-(s:ℝ))/(M:ℝ))*(j:ℝ))) =
      if r=s then (M:ℂ) else 0 := by
  change (∑ j : Fin M, (fun j : ℕ => (fun x : ℝ => (Real.probChar x : ℂ)) ((2*Real.pi*((r:ℝ)-(s:ℝ))/(M:ℝ))*(j:ℝ))) j)=_
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (fun x : ℝ => (Real.probChar x : ℂ)) ((2*Real.pi*((r:ℝ)-(s:ℝ))/(M:ℝ))*(j:ℝ))) M]
  exact exponential_sum_orthogonality M hM r s
private lemma modeCoeff_inner {L : ℕ} (hL : 0 < L) (r s : Fin L) :
    (∑ j : Fin (2*L), modeCoeff L r j*star (modeCoeff L s j)) =
      if r=s then (1/2:ℂ) else 0 := by
  classical
  let r' : Fin (2*L) := ⟨r.val,by have := r.isLt; omega⟩
  let s' : Fin (2*L) := ⟨s.val,by have := s.isLt; omega⟩
  have ht : ∀ j : Fin (2*L), modeCoeff L r j*star (modeCoeff L s j) =
      (modeScale L*modeScale L)*(fun x : ℝ => (Real.probChar x : ℂ)) ((2*Real.pi*((s':ℝ)-(r':ℝ))/((2*L:ℕ):ℝ))*(j:ℝ)) := by
    intro j
    rw [modeCoeff, modeCoeff, star_mul, modeScale_star, phase_star]
    calc
      _ = (modeScale L*modeScale L)*((fun x : ℝ => (Real.probChar x : ℂ)) (-(j:ℝ)*cycleFrequency L r)*(fun x : ℝ => (Real.probChar x : ℂ)) (-(-(j:ℝ)*cycleFrequency L s))) := by ring
      _ = _ := by
        rw [phase_mul]
        congr 2
        unfold cycleFrequency theta r' s'
        push_cast
        field_simp
        ring
  simp_rw [ht]
  rw [← Finset.mul_sum, phase_fin_orthogonality (by omega), modeScale_square hL]
  by_cases h : r=s
  · subst s
    simp only [r', s', ↓reduceIte]
    have hn : (L:ℂ)≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
    push_cast
    field_simp
    ring
  · have h' : s'≠ r' := by intro he; apply h; apply Fin.ext; have := congrArg Fin.val he; simpa [r',s'] using this.symm
    simp [h,h']
private lemma modeCoeff_bilinear {L : ℕ} (hL : 0 < L) (r s : Fin L) :
    (∑ j : Fin (2*L), modeCoeff L r j*modeCoeff L s j)=0 := by
  classical
  letI : NeZero (2*L) := ⟨by omega⟩
  let q : Fin (2*L) := ⟨r.val+s.val+1,by have := r.isLt; have := s.isLt; omega⟩
  have ht : ∀ j : Fin (2*L), modeCoeff L r j*modeCoeff L s j =
      (modeScale L*modeScale L)*(fun x : ℝ => (Real.probChar x : ℂ)) ((2*Real.pi*(((0:Fin (2*L)):ℝ)-(q:ℝ))/((2*L:ℕ):ℝ))*(j:ℝ)) := by
    intro j
    rw [modeCoeff, modeCoeff]
    calc
      _ = (modeScale L*modeScale L)*((fun x : ℝ => (Real.probChar x : ℂ)) (-(j:ℝ)*cycleFrequency L r)*(fun x : ℝ => (Real.probChar x : ℂ)) (-(j:ℝ)*cycleFrequency L s)) := by ring
      _ = _ := by
        rw [phase_mul]
        congr 2
        unfold cycleFrequency theta q
        push_cast
        simp only [Fin.val_zero,Nat.cast_zero]
        field_simp
        ring
  simp_rw [ht]
  rw [← Finset.mul_sum, phase_fin_orthogonality (by omega)]
  have hq : (0:Fin (2*L))≠ q := by
    intro he
    have hv := congrArg Fin.val he
    simp [q] at hv
  simp [hq]
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
def fourierMode {L : ℕ} (g : Fin (2*L) → R) (r : Fin L) : R :=
  Fintype.linearCombination ℂ g (modeCoeff L r)
private lemma fourierMode_CAR {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (r s : Fin L) :
    (fourierMode g r*fourierMode g s+fourierMode g s*fourierMode g r=0) ∧
    (fourierMode g r*star (fourierMode g s)+star (fourierMode g s)*fourierMode g r=
      (if r=s then (1:R) else 0)) := by
  constructor
  · rw [fourierMode, fourierMode, cliffordLinear_anticommutator g hsq hanti, modeCoeff_bilinear hL]
    simp
  · rw [fourierMode, fourierMode, cliffordLinear_star g hg,
      cliffordLinear_anticommutator g hsq hanti, modeCoeff_inner hL]
    split_ifs <;> norm_num
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
private lemma modeCoeff_unit_square {L : ℕ} (hL : 0 < L) (r : Fin L) :
    (∑ j : Fin (2*L), (modeCoeff L r j+star (modeCoeff L r j))*(modeCoeff L r j+star (modeCoeff L r j)))=1 := by
  classical
  have hbb := modeCoeff_bilinear hL r r
  have hbs := modeCoeff_inner hL r r
  have hss : (∑ j : Fin (2*L), star (modeCoeff L r j)*star (modeCoeff L r j))=0 := by
    simpa [star_sum,star_mul,mul_comm] using congrArg star hbb
  simp only [↓reduceIte] at hbs
  have he : ∀ j : Fin (2*L),
      (modeCoeff L r j+star (modeCoeff L r j))*(modeCoeff L r j+star (modeCoeff L r j))=
        modeCoeff L r j*modeCoeff L r j+2*(modeCoeff L r j*star (modeCoeff L r j))+
        star (modeCoeff L r j)*star (modeCoeff L r j) := by intro j; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hbb,hbs,hss]
  norm_num
def totalGamma {L : ℕ} (g : Fin (2*L) → R) (k : ℕ) : R :=
  if hk : k < 2*L then g ⟨k,hk⟩ else 0
def cliffordAverage {L : ℕ} (g : Fin (2*L) → R) : R →ₗ[ℂ] R := finiteTwirl (totalGamma g) (2*L)
private lemma cliffordAverage_invariant {L : ℕ} (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j))
    (j : Fin (2*L)) (X : R) : cliffordAverage g (g j*X*g j)=cliffordAverage g X := by
  have h := finiteTwirl_invariant (totalGamma g) (2*L)
    (by intro k hk; simpa [totalGamma,hk] using hsq ⟨k,hk⟩)
    (by intro k l hk hl hkl; simpa [totalGamma,hk,hl] using hanti ⟨k,hk⟩ ⟨l,hl⟩ (by simpa [Fin.ext_iff] using hkl))
    j.val j.isLt X
  simpa [totalGamma,j.isLt,cliffordAverage] using h
private lemma cliffordAverage_one {L : ℕ} (g : Fin (2*L) → R) (hsq : ∀ j, g j*g j=1) :
    cliffordAverage g 1=1 := by
  apply finiteTwirl_one
  intro j hj
  simpa [totalGamma,hj] using hsq ⟨j,hj⟩
def totalMode {L : ℕ} (g : Fin (2*L) → R) (k : ℕ) : R :=
  if hk : k < L then fourierMode g ⟨k,hk⟩ else 0
def numberProjection {L : ℕ} (g : Fin (2*L) → R) (k : ℕ) : R := totalMode g k*star (totalMode g k)
private def modeUnit {L : ℕ} (g : Fin (2*L) → R) (k : ℕ) : R := totalMode g k+star (totalMode g k)
def fourierVacuum {L : ℕ} (g : Fin (2*L) → R) : R := vacuumWord (numberProjection g) L
private lemma modeUnit_twirl {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k : ℕ) (hk : k < L) (X : R) :
    cliffordAverage g (modeUnit g k*X*modeUnit g k)=cliffordAverage g X := by
  have he : modeUnit g k=Fintype.linearCombination ℂ g (fun j => modeCoeff L ⟨k,hk⟩ j+star (modeCoeff L ⟨k,hk⟩ j)) := by
    simp [modeUnit,totalMode,hk,fourierMode,Fintype.linearCombination_apply,star_sum,star_smul,hg,add_smul,Finset.sum_add_distrib]
  rw [he]
  exact twirl_real_unit_invariance g hsq hanti (cliffordAverage g)
    (cliffordAverage_invariant g hsq hanti) _ (modeCoeff_unit_square hL ⟨k,hk⟩) X
private lemma totalMode_CAR {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k l : ℕ) (hk : k < L) (hl : l < L) :
    (totalMode g k*totalMode g l+totalMode g l*totalMode g k=0) ∧
    (totalMode g k*star (totalMode g l)+star (totalMode g l)*totalMode g k=if k=l then (1:R) else 0) := by
  simpa [totalMode,hk,hl,Fin.ext_iff] using fourierMode_CAR hL g hsq hg hanti ⟨k,hk⟩ ⟨l,hl⟩
private lemma numberProjection_star {L : ℕ} (g : Fin (2*L) → R) (k : ℕ) :
    star (numberProjection g k)=numberProjection g k := by simp [numberProjection,star_mul]
private lemma modeUnit_square {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k : ℕ) (hk : k < L) : modeUnit g k*modeUnit g k=1 := by
  have hc := totalMode_CAR hL g hsq hg hanti k k hk hk
  have hb := CAR_nilpotent _ hc.1
  have hs : star (totalMode g k)*star (totalMode g k)=0 := by simpa [star_mul] using congrArg star hb
  have hcar : totalMode g k*star (totalMode g k)+star (totalMode g k)*totalMode g k=1 := by simpa using hc.2
  unfold modeUnit
  simp only [add_mul,mul_add,hb,hs,zero_add,add_zero]
  simpa only [add_comm] using hcar
private lemma numberProjection_commute_mode {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k l : ℕ) (hk : k < L) (hl : l < L) (hne : k ≠ l) :
    totalMode g k*numberProjection g l=numberProjection g l*totalMode g k := by
  have hc := totalMode_CAR hL g hsq hg hanti k l hk hl
  have hb : totalMode g k*totalMode g l=-(totalMode g l*totalMode g k) := eq_neg_of_add_eq_zero_left hc.1
  have hbs : totalMode g k*star (totalMode g l)=-(star (totalMode g l)*totalMode g k) :=
    eq_neg_of_add_eq_zero_left (by simpa [hne] using hc.2)
  exact anticommute_commutes_number _ _ hb hbs
private lemma numberProjection_square {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k : ℕ) (hk : k < L) :
    numberProjection g k*numberProjection g k=numberProjection g k := by
  have hc := totalMode_CAR hL g hsq hg hanti k k hk hk
  exact CAR_projector_square _ (CAR_nilpotent _ hc.1) (by simpa using hc.2)
private lemma numberProjections_commute {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k l : ℕ) (hk : k < L) (hl : l < L) :
    numberProjection g k*numberProjection g l=numberProjection g l*numberProjection g k := by
  by_cases hne : k=l
  · subst l; rfl
  · have hc := totalMode_CAR hL g hsq hg hanti k l hk hl
    exact CAR_projectors_commute _ _ (eq_neg_of_add_eq_zero_left hc.1)
      (eq_neg_of_add_eq_zero_left (by simpa [hne] using hc.2))
private lemma modeUnit_flip {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k : ℕ) (hk : k < L) :
    modeUnit g k*numberProjection g k*modeUnit g k=1-numberProjection g k := by
  have hc := totalMode_CAR hL g hsq hg hanti k k hk hk
  exact CAR_flip_projector _ (CAR_nilpotent _ hc.1) (by simpa using hc.2)
private lemma modeUnit_fix {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (k l : ℕ) (hk : k < L) (hl : l < L) (hne : k ≠ l) :
    modeUnit g k*numberProjection g l*modeUnit g k=numberProjection g l := by
  have hb := numberProjection_commute_mode hL g hsq hg hanti k l hk hl hne
  have hbs : star (totalMode g k)*numberProjection g l=numberProjection g l*star (totalMode g k) := by
    have h := congrArg star hb
    simpa only [star_mul,numberProjection_star] using h.symm
  have hu : modeUnit g k*numberProjection g l=numberProjection g l*modeUnit g k := by
    rw [modeUnit,add_mul,mul_add,hb,hbs]
  rw [hu,mul_assoc,modeUnit_square hL g hsq hg hanti k hk,mul_one]
lemma fourierVacuum_properties {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    star (fourierVacuum g)=fourierVacuum g ∧
    fourierVacuum g*fourierVacuum g=fourierVacuum g ∧
    (∀ k, k < L → totalMode g k*fourierVacuum g=0 ∧ fourierVacuum g*star (totalMode g k)=0) ∧
      cliffordAverage g (fourierVacuum g)=((1/2:ℂ)^L) • (1:R) := by
  have hp := vacuumWord_projection (numberProjection g) L
    (fun k _ => numberProjection_star g k)
    (numberProjection_square hL g hsq hg hanti)
    (numberProjections_commute hL g hsq hg hanti)
  refine ⟨hp.1,hp.2,?_,?_⟩
  · intro k hk
    have hb : totalMode g k*numberProjection g k=0 := by
      have hc := totalMode_CAR hL g hsq hg hanti k k hk hk
      rw [numberProjection,← mul_assoc,CAR_nilpotent _ hc.1,zero_mul]
    have hz := vacuumWord_annihilate (numberProjection g) (totalMode g k) L k hk hb
      (fun l hl hlk => numberProjection_commute_mode hL g hsq hg hanti k l hk hl (Ne.symm hlk))
    refine ⟨hz,?_⟩
    simpa only [star_mul,star_zero,hp.1,fourierVacuum] using congrArg star hz
  · have hn := vacuum_twirl_normalization (cliffordAverage g) (numberProjection g) (modeUnit g) L
      (modeUnit_square hL g hsq hg hanti)
      (modeUnit_twirl hL g hsq hg hanti)
      (modeUnit_flip hL g hsq hg hanti)
      (fun k l hk hl => modeUnit_fix hL g hsq hg hanti k l hk (by omega) (by omega))
    rw [cliffordAverage_one g hsq] at hn
    exact hn
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped ComplexOrder
lemma fourierVacuum_psd {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) : (fourierVacuum g).PosSemidef := by
  apply vacuumWord_psd
  · intro k _; exact numberProjection_star g k
  · exact numberProjection_square hL g hsq hg hanti
  · exact numberProjections_commute hL g hsq hg hanti
end
noncomputable section
private lemma cycle_cosine_completeness {L : ℕ} (hL : 0 < L) (j k : Fin (2*L)) :
    (∑ r ∈ Finset.range L, Real.cos (((j:ℝ)-(k:ℝ))*(2*(r:ℝ)+1)*theta L)) =
      if j=k then (L:ℝ) else 0 := by
  classical
  by_cases he : j=k
  · subst k; simp
  · rw [if_neg he]
    let δ : ℝ := (j:ℝ)-(k:ℝ)
    have hθ := theta_pos hL
    have hLθ := theta_mul_L hL
    have hbound : -Real.pi < δ*theta L ∧ δ*theta L < Real.pi := by
      have hj : (j:ℝ)< 2*(L:ℝ) := by exact_mod_cast j.isLt
      have hk : (k:ℝ)< 2*(L:ℝ) := by exact_mod_cast k.isLt
      have hj0 : (0:ℝ)≤ j := by positivity
      have hk0 : (0:ℝ)≤ k := by positivity
      dsimp [δ]
      constructor <;> nlinarith
    have hδ : δ ≠ 0 := by
      intro hz
      have hval : j.val=k.val := by dsimp [δ] at hz; exact_mod_cast (sub_eq_zero.mp hz)
      exact he (Fin.ext hval)
    have hs : Real.sin (δ*theta L)≠ 0 := by
      by_cases hp : 0 < δ
      · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos hp hθ) hbound.2)
      · have hn : 0 < -δ := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hδ)
        have hpos := Real.sin_pos_of_pos_of_lt_pi (mul_pos hn hθ) (by nlinarith [hbound.1])
        rw [neg_mul,Real.sin_neg] at hpos
        linarith
    have hsin : Real.sin (δ*Real.pi)=0 := by
      have harg : δ*Real.pi=(((j.val:ℤ)-(k.val:ℤ):ℤ):ℝ)*Real.pi := by dsimp [δ]; push_cast; ring
      rw [harg,Real.sin_int_mul_pi]
    have hh := Real.sin_mul_sum_cos L (2*δ*theta L) (δ*theta L)
    have ha : (L:ℝ)*(2*δ*theta L)/2=δ*(Real.pi/2) := by nlinarith [hLθ]
    have hb : ((L:ℝ)-1)*(2*δ*theta L)/2+δ*theta L=δ*(Real.pi/2) := by nlinarith [hLθ]
    rw [show 2*δ*theta L/2=δ*theta L by ring,ha,hb] at hh
    have hzero : Real.sin (δ*(Real.pi/2))*Real.cos (δ*(Real.pi/2))=0 := by
      have hd := Real.sin_two_mul (δ*(Real.pi/2))
      rw [show 2*(δ*(Real.pi/2))=δ*Real.pi by ring,hsin] at hd
      nlinarith
    rw [hzero] at hh
    have hsum := (mul_eq_zero.mp hh).resolve_left hs
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    dsimp [δ]
    ring
private lemma modeCoeff_complete {L : ℕ} (hL : 0 < L) (j k : Fin (2*L)) :
    (∑ r : Fin L, 2*(star (modeCoeff L r j)*modeCoeff L r k+modeCoeff L r j*star (modeCoeff L r k))) =
      if j=k then (1:ℂ) else 0 := by
  classical
  have ht : ∀ r : Fin L,
      2*(star (modeCoeff L r j)*modeCoeff L r k+modeCoeff L r j*star (modeCoeff L r k)) =
        (4*(modeScale L*modeScale L))*(Real.cos (((j:ℝ)-(k:ℝ))*cycleFrequency L r):ℂ) := by
    intro r
    rw [modeCoeff,modeCoeff,star_mul,star_mul,modeScale_star,phase_star,phase_star,phase_cos]
    have h1 : -(-(j:ℝ)*cycleFrequency L r)+(-(k:ℝ)*cycleFrequency L r)=
      ((j:ℝ)-(k:ℝ))*cycleFrequency L r := by ring
    have h2 : (-(j:ℝ)*cycleFrequency L r)+ -(-(k:ℝ)*cycleFrequency L r)=
      -(((j:ℝ)-(k:ℝ))*cycleFrequency L r) := by ring
    calc
      _ = 2*(modeScale L*modeScale L)*((fun x : ℝ => (Real.probChar x : ℂ)) (-(-(j:ℝ)*cycleFrequency L r))*(fun x : ℝ => (Real.probChar x : ℂ)) (-(k:ℝ)*cycleFrequency L r)+
        (fun x : ℝ => (Real.probChar x : ℂ)) (-(j:ℝ)*cycleFrequency L r)*(fun x : ℝ => (Real.probChar x : ℂ)) (-(-(k:ℝ)*cycleFrequency L r))) := by ring
      _ = _ := by rw [phase_mul,phase_mul,h1,h2]; ring
  simp_rw [ht]
  rw [← Finset.mul_sum,modeScale_square hL,← Complex.ofReal_sum]
  have hsum : (∑ r : Fin L, Real.cos (((j:ℝ)-(k:ℝ))*cycleFrequency L r))=
      if j=k then (L:ℝ) else 0 := by
    simp only [cycleFrequency,← mul_assoc]
    change (∑ r : Fin L, (fun r : ℕ => Real.cos (((j:ℝ)-(k:ℝ))*(2*(r:ℝ)+1)*theta L)) r)=_
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Real.cos (((j:ℝ)-(k:ℝ))*(2*(r:ℝ)+1)*theta L)) L]
    exact cycle_cosine_completeness hL j k
  rw [hsum]
  by_cases he : j=k
  · rw [if_pos he,if_pos he]
    have hn : (L:ℂ)≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
    push_cast
    field_simp
  · simp [he]
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
private lemma fourierMode_reconstruct {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hg : ∀ j, star (g j)=g j) (j : Fin (2*L)) :
    (∑ r : Fin L, ((2*star (modeCoeff L r j)) • fourierMode g r +
      (2*modeCoeff L r j) • star (fourierMode g r)))=g j := by
  classical
  unfold fourierMode
  simp_rw [cliffordLinear_star g hg]
  simp only [Fintype.linearCombination_apply]
  simp only [Finset.smul_sum,smul_smul,← Finset.sum_add_distrib,← add_smul]
  rw [Finset.sum_comm]
  have ht : ∀ k : Fin (2*L),
      (∑ r : Fin L, (2*star (modeCoeff L r j)*modeCoeff L r k+
        2*modeCoeff L r j*star (modeCoeff L r k)) • g k) =
        (if j=k then (1:ℂ) else 0) • g k := by
    intro k
    rw [← Finset.sum_smul]
    congr 1
    convert modeCoeff_complete hL j k using 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp_rw [ht]
  simp
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
private lemma fourierVacuum_contractions {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (r s : Fin L) :
    cliffordAverage g (fourierMode g r*fourierMode g s*fourierVacuum g)=0 ∧
    cliffordAverage g (star (fourierMode g r)*fourierMode g s*fourierVacuum g)=0 ∧
    cliffordAverage g (fourierMode g r*star (fourierMode g s)*fourierVacuum g)=
      (if r=s then (1:ℂ) else 0) • cliffordAverage g (fourierVacuum g) ∧
    cliffordAverage g (star (fourierMode g r)*star (fourierMode g s)*fourierVacuum g)=0 := by
  classical
  have hv := fourierVacuum_properties hL g hsq hg hanti
  have hr := hv.2.2.1 r.val r.isLt
  have hs := hv.2.2.1 s.val s.isLt
  simp only [totalMode,dif_pos r.isLt,dif_pos s.isLt] at hr hs
  have hc := (fourierMode_CAR hL g hsq hg hanti r s).2
  have hc' : fourierMode g r*star (fourierMode g s)+star (fourierMode g s)*fourierMode g r=
      (if r=s then (1:ℂ) else 0) • (1:R) := by
    simpa only [ite_smul,one_smul,zero_smul] using hc
  apply vacuum_pair_contractions (cliffordAverage g) _ _ _ _ hr.1 hs.1 hc' _ hr.2
  intro X
  rw [fourierMode,cliffordLinear_star g hg]
  exact twirl_linear_cyclic g hsq (cliffordAverage g) (cliffordAverage_invariant g hsq hanti) _ X
lemma fourierVacuum_covariance {L : ℕ} (hL : 0 < L) (g : Fin (2*L) → R)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (j k : Fin (2*L)) :
    cliffordAverage g (g j*g k*fourierVacuum g)=
      (4*∑ r : Fin L, star (modeCoeff L r j)*modeCoeff L r k) •
        cliffordAverage g (fourierVacuum g) := by
  classical
  have hc := fourierVacuum_contractions hL g hsq hg hanti
  rw [← fourierMode_reconstruct hL g hg j,← fourierMode_reconstruct hL g hg k]
  simp only [Finset.sum_mul,Finset.mul_sum,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    smul_smul,map_sum,map_add,map_smul]
  simp_rw [(hc _ _).1,(hc _ _).2.1,(hc _ _).2.2.1,(hc _ _).2.2.2]
  simp only [smul_zero,zero_add,add_zero,smul_smul,ite_smul,one_smul,zero_smul]
  simp only [Finset.sum_const_zero,smul_zero,zero_add,smul_ite,smul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,smul_smul]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  ring
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
