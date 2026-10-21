/- GID: D5/S3/Quantum/Transport/StrongAbsorptionMoments
   generality: I
   mirror-B: D5/B/S3/Quantum/Transport/StrongAbsorptionMoments
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Strong-absorption spectral and Wigner moments. -/

/-
admission_basis: open-problem-resolution (#19346; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19485
proof_shape: bind-only for traceQPow, claim54, claim55, claim, expJet_one, expJet_two, cubicDeriv, cubicDeriv_X, cubicDeriv_difference, cubicDeriv_delta, cubicDeriv_total, pair_quadratic_sum, cubicDeriv_delta_eval, polyIntegral_X_cube, laguerre_cubic_ibp, singleBaseExpectation, singleBaseExpectation_one, singleBaseExpectation_a_power, singleBaseExpectation_a, singleBaseExpectation_a_sq, singleBaseExpectation_t, polyIntegral_weighted, singleBaseExpectation_c, baseExpectation_tensor, expJet_three, singleBaseExpectation_a_cube, singleWMoment_one, singleBaseExpectation_at, baseMap, baseMap_C_mul, baseMap_tensor, baseMap_left, baseMap_right, linearDensityPoly_rename, quadraticDensityPoly_rename, baseExpectation_density_two, a_quadraticDensityPoly_rename, baseExpectation_a_density_two, baseExpectation_t_density_one, correctionJet_one, rescaled_first_moment, rescaled_second_moment, rescaled_moments_bounded, inv_pow_bigO, FirstOrder.sub_const_bigO, bounded_times_inv_power, finite_binomial_second_order, tauW_moment_binomial, bigO_inv_pow_bound, wigner_normalized_second_order, result55, rescaled_delay_bounds, rescaled_delay_linear_error, rescaled_delay_cubic_remainder, rescaled_delay_square_remainder, rescaled_delay_cube_remainder, spectralPoly, spectralRescaled, spectralPoly_eval, baseExpectation_a_density_one, baseExpectation_spectral_low, law_spectral_one_second, law_spectral_two_first, law_spectral_three_first, law_remainder_power, spectralRescaled_bounds, spectralRescaled_integrable, spectralRescaled_moments_bounded, average_abs_bound, spectralRescaled_jet_bounds, spectralRescaled_integral_jets, cast_choose_three, finite_binomial_third_order, spectral_moments_low, traceQPow_moment_binomial, spectral_normalized_third_order, result54, result.
Consumers: each helper is used by the later estimates or moment assembly; result is terminal.
Frozen dependency identities at merged base (declaration statement_id; publicized names correspond to their original private declarations): D5.S3.Quantum.Transport.StrongAbsorption.Density.basePolynomial_integrable = sha256:0db1c7d896c7af185e002ed8398e75cf169d275a3d5712a7d65ae6607ecbe8d6; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight = sha256:d96d00410d62d0396fa5f38bce6c50b759eb11b615d463ac7dca53e02a2db8ef; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_eq_zero_off_orthant = sha256:e961e3166d1030f27fac872a3825253ddd24c5b966694a098f2ef15bee5ac663; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_mass = sha256:a8fde99342f74b451374925bfab2d86e62f9a360cea356718612c5a7aaaaf322; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_nonneg = sha256:913f42546ef9347276bddeff402ec1d793054c584bb44f6f0f2e64ee5c2f041e; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly = sha256:4c541a4d04a8d5a26474bdad91a91c9059ad8137f4144a6c336ce99ad5f1b14d; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly_eval = sha256:4dbd2cfee317204a8c01ef2dd1cf1e97f00a529f7b582a2512b027c31aaede0c; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly_nonneg = sha256:24c1ec53838b9333ad61c93c495186b0100d3fc715e11a6156329fdec7b66f04; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossIntegral = sha256:a83281407227967bab7c49a37db404fa3e23a47b5f222d8a2692e4620217d08c; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossIntegrand_integrable = sha256:4e861e34a0c66536fcabeba4d468cf6d6f5356a7cc0d78b4d62f2826f12d93a5; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct = sha256:90840c7537cfd9a02e1abb8a2049d58bcb65d94e52a7ad37831668f465836dac; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct_abs_bound = sha256:2e8512e2c0ef3b1243dca6a74e07d48850540916680bfc979b3a0a2b8eb02c4a; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct_firstOrder = sha256:a7fc0bfa3a4fcecd92f2e5a788bf812977c20034fa4a26fde87f6e9a297fdd68; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral = sha256:9c176103775259e2c2aadd2065acc6ea8f69b0a3aebe9cfe01eb769953e931c3; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral_eq_sub = sha256:8a98afcac2020d8555494797bc90eb90257f94455a1bba9105d1acf0fd52abf9; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral_firstOrder = sha256:09952645d6123ec0a13b1cacdabdd4fc28d8678d099ea66c48c8700f14c75234; D5.S3.Quantum.Transport.StrongAbsorption.Density.jointSum = sha256:e601501386bd621533f446a63c1f11643b99f719c59f8b84c21c169e4d143bcc; D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_firstOrder = sha256:3f89da36a7246dc32b351aadc61149995c8e2a483d6600f33a67ef11cb732771; D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_ratio = sha256:fb5e31de612d0a99059f93046298c707d053488f868a2c679156663640b260f1; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityIntegral_zero = sha256:5867026755d3e1a2d5d7f7e2ec7b1e04c8a1029c34c6af7917c902fbee0ad1df; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityPoly = sha256:33e1d063c468969aaae34e14f1d799a5f10bed07712cd895b5a6e910bdfbb96a; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityPoly_eval = sha256:5d6654e44de6dd05bf279eb8114e4c404e9d4816beea39e955900735ea4c35b9; D5.S3.Quantum.Transport.StrongAbsorption.Density.tailSet = sha256:9e7b8c0441bcc3719db366bac6de23c71949f8172f493897b7aaa01ee7ae79e9; D5.S3.Quantum.Transport.StrongAbsorption.Density.tail_family_exponential_bound = sha256:5e332bf574285f956b157411ad2a74c0689d4ceea3650b45b423e2df7e1e5f24; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.FirstOrder = sha256:b464864096def8aa1bad012b7955b44cf3f4e556a523d4905b952b7c4baa6c8d; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.FirstOrder.tendsto = sha256:458b3da540ff254b6898c6742b4f4a61aeeb9265697d2d54787d7ad02be4c896; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.correctionCGF = sha256:6d29f984373ccf1b5b90b29a70a9339c6a47658ce0f00aa30cb64fc19ed594c9; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.correctionCGF._proof_1 = sha256:c41dd7b06243201be025ed65dc535a5ec3235a2cfc4826e8022fe6bc3156e61d; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.correctionCGF_iterated = sha256:aa9181a39785e3233065609332c9411dc66bc193e0f2cc6b669e7dd0b5b7e1be; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.gammaCGF = sha256:aacb97210029a39ec21a9e1e9a8c7ef84b7d80e99f140857a7fba12a25b8870d; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.gammaCGF_deriv = sha256:339246e2dbce74ba9a5d67dd128e3985782838c8b5c894d504b83ae4891a22e5; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.gammaCGF_iterated = sha256:bcd599cc57b1a92352043df138237a6c8955c8d0296493d351291261a70b4f3b; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.inverseSlope = sha256:efbf8278c153c2de5b8c471613671aa49cb4fe4ebe1d9683f5d9501e8a610026; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.inverseSlope_deriv = sha256:6302659efd5eb7bc01f4afaabb487dc7d49945f33de555c2e57a0c3e97dd5d06; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.law = sha256:234165c5a68f4041955a51a3f8cb7722d9ba23a543b735e842287b1f79724b97; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.law_ae_support = sha256:8c80b1b050ddc5cae847ef430864d67ef889d9b24c95815672c179d7a8803a6e; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.law_isProbability = sha256:ced7b457a76cb2c73b20eaa3ea04184f7cbb2808bad8764c7221335065563ef1; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.orthantMeasure = sha256:2a110aa6d978ec1286ba0c6e7ce92f241a6bc6c221b7ffec75a1f2e4529bf8a2; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum = sha256:352ce62e479e89ad44b697993c67367cccafda15b1d46b4e65122834c75849c4; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum.eq_1 = sha256:c4a269e69dc38b50b7557ebe841c011815d8016dda4a5cc1cee5b47f63b7e17b; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.rescaledObservable = sha256:e53ad8359841b2fafaa03a5825b0cbba612c2956063bc4d89f8f95f74b9e7797; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.supportSet = sha256:1e61d1223f2ca24b730b8931df8e695e3dc4f5894bdd31ad4eeede7d65724059; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.supportSet_membership = sha256:fdbbe6381aab6ac6da95ea9f570c06587b6cc98346f89984711b131cf068d882; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.tauW = sha256:35c7c2aacf7e8bcac3a12bab6720880e757f715b0d547857cfa12dbd14ef2d78; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correctionCGF_analytic = sha256:7e946c4fc77252aa19a2415db292af3289c11ba98ee308b287fd593b9bb1460d; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correctionJet = sha256:19c9d919f7259940b1508c06e7c24c0c7b0d505777d5a28dcdf1267748c887b9; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correction_jet_recurrence = sha256:47fee0cce558c2f939da00c48102ee6c920abff4b7be2a08c058587a30c6ee32; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaPoly = sha256:fc4b792ffa8f66cb20b2cd29da83144e1656edfdffb7da264ff903923a41fcd3; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaPoly_eval = sha256:29bd0870eb5dd97e5532a2db378450c1a5e6387cfe7e7f0fff6f7e6cccaf3065; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq = sha256:0ec83e1ff1454bc63ae4cc5ecce729ab8f9b69dd1e38013e5db8a38912da32c9; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.derivation_product_eigen = sha256:2c3cf7c80693f43784ea4121a8f3d48de604ef2029df4d7f14dcbe62bf6294ef; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.expJet = sha256:969f629a64dee5abced4531c93543b4f70fe461becc070ce8678e7287c3fd29b; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.exp_jet_recurrence = sha256:b0a75d95467bd7768671d87a458d34d03838e7026e5e9f96ce6190fa3e20f0ea; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.gammaCGF_analytic = sha256:69ca16a906e469aa32cb6db92a0f082d70789891c1d4993eff71b558d1f2af0f; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated = sha256:f91ef86637f3144c730c7fa865699b9e9b95c1bb53d8453eb434fdfd0b52d163; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw = sha256:ebc4de3dbf39e8c01bb0bd032eedf88fc2fbc719e294484016c8a9b5858d9a6f; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_near = sha256:77c40d552f27547ea9716ce96a4345076079b8f9c4da9813f943483711bd1c4e; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreMoment = sha256:b50183739a9b5fef7815c0d932096bc45493c972eb5b2b9a87783051db84fa54; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight = sha256:47e41520a7268c89cf136c04772c1fef4d9af106274e2a8d51d1e0bc29d2d0c3; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p2 = sha256:d973e20455e787ec2352d1b733aa802922befd79635a03723be4961ec35655c6; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.orthant_measure = sha256:65d31ab455a6a2e3ecd9e2db10c34bcf6c8ad801836fc4ebf17733804b8241bd; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition = sha256:db7289f09641ff884c230527f9df4880ff3fc29a942837cf011b5ba39670daf1; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos = sha256:d09595e6e604883819d6f3859e5f7bcdc2510a00edcf51645c7a340cd12a5bea; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral = sha256:bd2d274e8787005abe85483d95176ce2a959331dcbb7815a3c0b127b4212942e; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_sq = sha256:bf0a4f4bd3a82084064a59052783f68160884ff8c91da57ae2114825d1bd8d39; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_add = sha256:4ed94578b31e638dcb13bf095f3f424fe5b707ecbbfc89ca27a16799c8057e41; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_sum = sha256:208b50b94d59f4ef5689e30d555b8986d3126e7a8f5a3408c3179f0957fd0616; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polynomial_exp_integrable_single = sha256:53cbb063be1d928eaf08a87a165f538983edfc0d82bfe29875296b6787b04bd7; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation = sha256:599ccfbb507300a01cad591bc345b28869d69370df77633e1b69a23f2b77db6e; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_add = sha256:5f1c1854a3213a98a9781d0e6ccc05ac2740f9be1880b787dcbdf7c6c3817bf4; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.law_polynomial_integrable = sha256:34b0da626eaefb655f539a64ce590c12dd2bae7b5192ccf360fbb634bdbe1b1c; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion = sha256:f8c05f5269d53acb67979ff1633692b900a141e8558f2f6713bbd52ad265e218; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_pow_integrable = sha256:12aaf4b1adabc66117837bf9b191fdd5ef6c4ff0ed9ae056c9c77782f6401b5b; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment = sha256:7d48513f6aa02a1440c46a14954c7f0206e6bc369ad9633968417beca471f7f7; D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative = sha256:7212e8a4d792aad62dfacd81ae8f9ae581c43067a86e9d0e27cf9fc22bde214e.
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
import D5.S3.Quantum.Transport.StrongAbsorption.Density
import D5.S3.Quantum.Transport.StrongAbsorptionCumulants
import D5.S3.Quantum.Transport.StrongAbsorption.SecondOrderDensity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace D5.S3.Quantum.Transport.StrongAbsorptionMoments
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations
open D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
open D5.S3.Quantum.Transport.StrongAbsorption.Density
open D5.S3.Quantum.Transport.StrongAbsorptionCumulants
open D5.S3.Quantum.Transport.StrongAbsorption.SecondOrderDensity
open MeasureTheory ProbabilityTheory Set Real Finset Filter Asymptotics MvPolynomial
open scoped Topology
set_option maxHeartbeats 2000000

noncomputable def traceQPow (M n : ℕ) (γ : ℝ) (p : (Fin M → ℝ) × (Fin M → ℝ)) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, (1 / (γ + p.1 i)) ^ n

/-- Eq. (54): `(1/M)⟨Tr(Qⁿ)⟩ = 1/γⁿ − n/γⁿ⁺¹ + n²/γⁿ⁺² − (n+1)[n(5n−2)M² + n(n+2)]/(6M²γⁿ⁺³) + O(γ^(−n−4))`. -/

def claim54 : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ n : ℕ, 1 ≤ n → ∃ C γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ →
    |(∫ p, traceQPow M n γ p ∂(law M γ)) -
      (1 / γ ^ n - n / γ ^ (n + 1) + (n : ℝ) ^ 2 / γ ^ (n + 2) -
        (n + 1) * (n * (5 * n - 2) * (M : ℝ) ^ 2 + n * (n + 2)) / (6 * (M : ℝ) ^ 2 * γ ^ (n + 3)))| ≤
      C / γ ^ (n + 4)

/-- Eq. (55): `(1/Mⁿ)⟨[Tr(Q)]ⁿ⟩ = 1/γⁿ − n/γⁿ⁺¹ + n[(n+1)M² + (n−1)]/(2M²γⁿ⁺²) + O(γ^(−n−3))`, where
`Tr(Q)/M` is the Wigner time delay `tauW`. -/

def claim55 : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ n : ℕ, 1 ≤ n → ∃ C γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ →
    |(∫ p, tauW M γ p ^ n ∂(law M γ)) -
      (1 / γ ^ n - n / γ ^ (n + 1) + n * ((n + 1) * (M : ℝ) ^ 2 + (n - 1)) / (2 * (M : ℝ) ^ 2 * γ ^ (n + 2)))| ≤
      C / γ ^ (n + 3)

/-- The conjecture following Eq. (53): "(54) … and (55) … for every positive integer n". -/

def claim : Prop := claim54 ∧ claim55
private theorem expJet_one {d : ℝ} (hd : d ≠ 0) : expJet (gammaCGF d) 1 = 1 := by
  have h := exp_jet_recurrence (gammaCGF_analytic d) (by simp [gammaCGF]) 0
  rw [gammaCGF_iterated hd 0] at h
  simpa using h.symm
private theorem expJet_two {d : ℝ} (hd : d ≠ 0) : expJet (gammaCGF d) 2 = 1 + d⁻¹ := by
  have h := exp_jet_recurrence (gammaCGF_analytic d) (by simp [gammaCGF]) 1
  norm_num [gammaCGF_iterated hd, expJet_one hd] at h
  linarith
private noncomputable def cubicDeriv (M : ℕ) : Derivation ℝ (MvPolynomial (Fin M) ℝ) (MvPolynomial (Fin M) ℝ) :=
  MvPolynomial.mkDerivation ℝ fun i => (X i)^3
private theorem cubicDeriv_X (M : ℕ) (i : Fin M) : cubicDeriv M (X i) = (X i)^3 := by
  simp [cubicDeriv, MvPolynomial.mkDerivation_X]
private theorem cubicDeriv_difference (M : ℕ) (i j : Fin M) :
    cubicDeriv M ((X i-X j)^2) = 2*((X i)^2+X i*X j+(X j)^2)*(X i-X j)^2 := by
  simp only [Derivation.leibniz_pow, map_sub, cubicDeriv_X, nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring
private theorem cubicDeriv_delta (M : ℕ) :
    cubicDeriv M (deltaPoly M) =
      (∑ i, ∑ j, if i < j then 2*((X i)^2+X i*X j+(X j)^2) else 0)*deltaPoly M := by
  unfold deltaPoly
  apply derivation_product_eigen
  intro i _
  apply derivation_product_eigen
  intro j _
  split_ifs
  · exact cubicDeriv_difference M i j
  · simp
private theorem cubicDeriv_total (M : ℕ) (P : MvPolynomial (Fin M) ℝ) :
    cubicDeriv M P = ∑ i, (X i)^3 * MvPolynomial.pderiv i P := by
  have he : cubicDeriv M = ∑ i : Fin M, (X i : MvPolynomial (Fin M) ℝ)^3 • MvPolynomial.pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [cubicDeriv_X, Derivation.smul_apply, MvPolynomial.pderiv_X,
      Pi.single_apply, smul_eq_mul]
  rw [he]
  simp [Derivation.smul_apply, smul_eq_mul]
private theorem pair_quadratic_sum (M : ℕ) (v : Fin M → ℝ) :
    (∑ i, ∑ j, if i < j then 2*(v i^2+v i*v j+v j^2) else 0) =
      (2*(M : ℝ)-3)*(∑ i, v i^2)+(∑ i, v i)^2 := by
  let S := ∑ i, ∑ j, if i < j then v i^2+v i*v j+v j^2 else 0
  have hswap : (∑ i, ∑ j, if j < i then v i^2+v i*v j+v j^2 else 0) = S := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have he (i j : Fin M) :
      (if i < j then v i^2+v i*v j+v j^2 else 0) +
        (if j < i then v i^2+v i*v j+v j^2 else 0) =
      (v i^2+v i*v j+v j^2)-(if i = j then 3*v i^2 else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · subst j; simp; ring
    · simp [h, not_lt.mpr h.le, ne_of_gt h]
  have h2 : S+S =
      (∑ i, ∑ j, (v i^2+v i*v j+v j^2)) - 3*(∑ i, v i^2) := by
    calc
      S+S = ∑ i, ∑ j,
          ((if i < j then v i^2+v i*v j+v j^2 else 0)+(if j < i then v i^2+v i*v j+v j^2 else 0)) := by
            simp only [Finset.sum_add_distrib, hswap, S]
      _ = _ := by simp_rw [he]; simp [Finset.sum_sub_distrib, Finset.mul_sum]
  have hfull : (∑ i, ∑ j, (v i^2+v i*v j+v j^2)) =
      2*(M : ℝ)*(∑ i, v i^2)+(∑ i, v i)^2 := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
    ring
  have heS : (∑ i, ∑ j, if i < j then 2*(v i^2+v i*v j+v j^2) else 0) = 2*S := by
    dsimp [S]
    simp only [mul_ite, mul_zero, Finset.mul_sum]
  rw [heS]
  rw [hfull] at h2
  linarith
private theorem cubicDeriv_delta_eval (M : ℕ) (x : Fin M → ℝ) :
    eval x (cubicDeriv M (deltaPoly M)) =
      ((2*(M : ℝ)-3)*(∑ i, x i^2)+(∑ i, x i)^2)*deltaSq M x := by
  rw [cubicDeriv_delta, map_mul, deltaPoly_eval]
  simp only [map_sum, apply_ite, map_mul, map_ofNat, map_pow, MvPolynomial.eval_X, map_add, map_zero]
  rw [pair_quadratic_sum]
private theorem polyIntegral_X_cube {M : ℕ} {a : ℝ} (ha : 0<a) (i : Fin M) (P : MvPolynomial (Fin M) ℝ) :
    a*polyIntegral a ((X i)^3*P) =
      3*polyIntegral a ((X i)^2*P)+polyIntegral a ((X i)^3*MvPolynomial.pderiv i P) := by
  have h := polyIntegral_X_sq ha i (X i*P)
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, one_mul] at h
  have h1 : (X i)^2*(X i*P) = (X i)^3*P := by ring
  have h2 : X i*(X i*P) = (X i)^2*P := by ring
  have h3 : (X i)^2*(P+X i*MvPolynomial.pderiv i P) =
      (X i)^2*P+(X i)^3*MvPolynomial.pderiv i P := by ring
  rw [h1,h2,h3,polyIntegral_add ha] at h
  linarith
private theorem laguerre_cubic_ibp {M : ℕ} {a : ℝ} (ha : 0<a) :
    a*polyIntegral a ((∑ i : Fin M, (X i)^3)*deltaPoly M) =
      2*(M : ℝ)*polyIntegral a ((∑ i : Fin M, (X i)^2)*deltaPoly M)+
        polyIntegral a ((∑ i : Fin M, X i)^2*deltaPoly M) := by
  have he : polyIntegral a (cubicDeriv M (deltaPoly M)) =
      (2*(M : ℝ)-3)*polyIntegral a ((∑ i : Fin M, (X i)^2)*deltaPoly M)+
        polyIntegral a ((∑ i : Fin M, X i)^2*deltaPoly M) := by
    unfold polyIntegral
    simp only [cubicDeriv_delta_eval, map_mul, map_sum, map_pow, MvPolynomial.eval_X, deltaPoly_eval]
    rw [show (fun x : Fin M → ℝ => Real.exp (-a*∑ i, x i)*
        (((2*(M : ℝ)-3)*(∑ i, x i^2)+(∑ i, x i)^2)*deltaSq M x)) =
        (fun x => (2*(M : ℝ)-3)*(Real.exp (-a*∑ i, x i)*((∑ i, x i^2)*deltaSq M x))+
          Real.exp (-a*∑ i, x i)*((∑ i, x i)^2*deltaSq M x)) by funext x; ring,
      integral_add, integral_const_mul]
    · apply ((polynomial_exp_integrable_single ha ((∑ i : Fin M, (X i)^2)*deltaPoly M)).const_mul (2*(M : ℝ)-3)).congr
      filter_upwards [] with x
      simp only [MvPolynomial.eval_mul,MvPolynomial.eval_sum,MvPolynomial.eval_pow,MvPolynomial.eval_X,deltaPoly_eval]
    · apply (polynomial_exp_integrable_single ha ((∑ i : Fin M, X i)^2*deltaPoly M)).congr
      filter_upwards [] with x
      simp only [MvPolynomial.eval_mul,MvPolynomial.eval_sum,MvPolynomial.eval_pow,MvPolynomial.eval_X,deltaPoly_eval]

  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => polyIntegral_X_cube ha i (deltaPoly M))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← polyIntegral_sum ha, ← polyIntegral_sum ha, ← polyIntegral_sum ha,
    ← cubicDeriv_total] at h
  simp only [← Finset.sum_mul] at h
  linarith
private noncomputable def singleBaseExpectation (M : ℕ) (P : MvPolynomial (Fin M) ℝ) : ℝ :=
  (∫ x, laguerreWeight M M x*eval x P)/partition M M
private theorem singleBaseExpectation_one {M : ℕ} (hM : 1≤M) : singleBaseExpectation M 1=1 := by
  simp only [singleBaseExpectation,map_one,mul_one]
  exact div_self (partition_pos M (Nat.cast_pos'.mpr hM)).ne'
private theorem singleBaseExpectation_a_power {M : ℕ} (hM : 1≤M) (r : ℕ) :
    singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)^r) = (M : ℝ)^r*expJet (gammaCGF ((M : ℝ)^2)) r := by
  have hA (x : Fin M → ℝ) : eval x ((MvPolynomial.psum (Fin M) ℝ 1)) = (M : ℝ)*Finset.univ.expect x := by
    simp only [MvPolynomial.psum,pow_one,map_sum,eval_X]
    simpa only [Fintype.card_fin] using (Fintype.card_mul_expect x).symm
  have he : (fun x : Fin M → ℝ => laguerreWeight M M x*eval x ((MvPolynomial.psum (Fin M) ℝ 1)^r)) =
      (fun x => (M : ℝ)^r*(laguerreWeight M M x*(Finset.univ.expect x)^r)) := by
    funext x
    rw [map_pow,hA,mul_pow]
    ring
  unfold singleBaseExpectation
  rw [he,integral_const_mul,mul_div_assoc,laguerreH_iterated hM r]
private theorem singleBaseExpectation_a {M : ℕ} (hM : 1≤M) : singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)) = M := by
  have hm : (M : ℝ)^2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM))
  simpa only [pow_one,expJet_one hm,mul_one] using singleBaseExpectation_a_power hM 1
private theorem singleBaseExpectation_a_sq {M : ℕ} (hM : 1≤M) :
    singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)^2) = (M : ℝ)^2+1 := by
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  rw [singleBaseExpectation_a_power hM 2,expJet_two (pow_ne_zero _ hm)]
  field_simp [hm]
private theorem singleBaseExpectation_t {M : ℕ} (hM : 1≤M) : singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 2)) = 2*(M : ℝ) := by
  have hm : 0<(M : ℝ) := Nat.cast_pos'.mpr hM
  calc
    _ = laguerreMoment M 2 M := by simp [singleBaseExpectation,MvPolynomial.psum,laguerreMoment,map_sum,mul_comm]
    _ = 2*(M : ℝ)^3/(M : ℝ)^2 := laguerre_p2 hm
    _ = _ := by field_simp [hm.ne']
private theorem polyIntegral_weighted {M : ℕ} (a : ℝ) (P : MvPolynomial (Fin M) ℝ) :
    polyIntegral a (P*deltaPoly M) = ∫ x, laguerreWeight M a x*eval x P := by
  unfold polyIntegral
  rw [← orthant_measure, ← integral_indicator measurableSet_Ici]
  congr 1
  funext x
  have hx' : x ∈ Set.Ici (0 : Fin M → ℝ) ↔ ∀ i, 0≤x i := Iff.rfl
  by_cases hx : ∀ i, 0≤x i
  · simp [Set.indicator,hx',hx,laguerreWeight,map_mul,deltaPoly_eval,mul_comm,mul_left_comm,mul_assoc]
  · simp [Set.indicator,hx',hx,laguerreWeight,map_mul,deltaPoly_eval]
private theorem singleBaseExpectation_c {M : ℕ} (hM : 1≤M) :
    singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 3)) = 5*(M : ℝ)+(M : ℝ)⁻¹ := by
  have hm : 0<(M : ℝ) := Nat.cast_pos'.mpr hM
  have h := laguerre_cubic_ibp (M := M) hm
  simp only [polyIntegral_weighted] at h
  have hh : (M : ℝ)*singleBaseExpectation M (MvPolynomial.psum (Fin M) ℝ 3) =
      2*(M : ℝ)*singleBaseExpectation M (MvPolynomial.psum (Fin M) ℝ 2)+
        singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)^2) := by
    simpa only [singleBaseExpectation, MvPolynomial.psum, pow_one, add_div, mul_div_assoc]
      using congrArg (fun z : ℝ => z/partition M M) h
  rw [singleBaseExpectation_t hM,singleBaseExpectation_a_sq hM] at hh
  apply (mul_left_cancel₀ hm.ne')
  calc
    (M : ℝ)*singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 3)) = 5*(M : ℝ)^2+1 := by nlinarith [hh]
    _ = (M : ℝ)*(5*(M : ℝ)+(M : ℝ)⁻¹) := by rw [mul_add,mul_inv_cancel₀ hm.ne']; ring
private theorem baseExpectation_tensor {M : ℕ} (hM : 1≤M) (P Q : MvPolynomial (Fin M) ℝ) :
    baseExpectation M (rename Sum.inl P*rename Sum.inr Q) =
      singleBaseExpectation M P*singleBaseExpectation M Q := by
  have hz : partition M M ≠ 0 := (partition_pos M (Nat.cast_pos'.mpr hM)).ne'
  have he : (fun p => baseWeight M M p*eval (Sum.elim p.1 p.2) (rename Sum.inl P*rename Sum.inr Q)) =
      (fun p : (Fin M → ℝ) × (Fin M → ℝ) =>
        (laguerreWeight M M p.1*eval p.1 P)*(laguerreWeight M M p.2*eval p.2 Q)) := by
    funext p
    simp only [baseWeight,map_mul,eval_rename,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    ring
  unfold baseExpectation singleBaseExpectation
  rw [he,Measure.volume_eq_prod,
    integral_prod_mul (fun x : Fin M → ℝ => laguerreWeight M M x*eval x P)
      (fun y : Fin M → ℝ => laguerreWeight M M y*eval y Q)]
  field_simp
  <;> ring
private theorem expJet_three {d : ℝ} (hd : d≠0) :
    expJet (gammaCGF d) 3 = 1+3*d⁻¹+2*d⁻¹^2 := by
  have h := exp_jet_recurrence (gammaCGF_analytic d) (by simp [gammaCGF]) 2
  norm_num [Finset.sum_range_succ,gammaCGF_iterated hd,expJet_one hd,expJet_two hd] at h
  simp only [div_eq_mul_inv,←inv_pow] at h
  linarith
private theorem singleBaseExpectation_a_cube {M : ℕ} (hM : 1≤M) :
    singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)^3) = (M : ℝ)^3+3*(M : ℝ)+2/(M : ℝ) := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  rw [singleBaseExpectation_a_power hM 3,expJet_three (pow_ne_zero _ hm)]
  field_simp [hm]
  <;> ring
private theorem singleWMoment_one {M : ℕ} (hM : 1≤M) :
    singleWMoment M 1 = 2+4/((M : ℝ)^2) := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  have hd : (M : ℝ)^2≠0 := pow_ne_zero _ hm
  rw [singleWMoment_derivative hM 1,iteratedDeriv_one,
    (laguerreHw_near hM).deriv_eq]
  have hK : DifferentiableAt ℝ (gammaCGF ((M : ℝ)^2)) 0 :=
    (gammaCGF_analytic _).differentiableAt
  have hS : DifferentiableAt ℝ (inverseSlope ((M : ℝ)^2)) 0 := by
    unfold inverseSlope
    fun_prop (disch := simp)
  have hKd := hK.hasDerivAt
  rw [gammaCGF_deriv hd] at hKd
  have hSd := hS.hasDerivAt
  rw [inverseSlope_deriv] at hSd
  have h := ((hKd.exp.const_mul 2).mul (hSd.pow 2)).deriv
  convert h using 1 <;> norm_num [gammaCGF,inverseSlope,div_eq_mul_inv] <;> ring
private theorem singleBaseExpectation_at {M : ℕ} (hM : 1≤M) :
    singleBaseExpectation M ((MvPolynomial.psum (Fin M) ℝ 1)*(MvPolynomial.psum (Fin M) ℝ 2)) = 2*(M : ℝ)^2+4 := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  have he : (fun x : Fin M → ℝ => laguerreWeight M M x*eval x ((MvPolynomial.psum (Fin M) ℝ 1)*(MvPolynomial.psum (Fin M) ℝ 2))) =
      (fun x => (M : ℝ)^2*(laguerreWeight M M x*(Finset.univ.expect (fun i => x i^2))*(Finset.univ.expect x)^1)) := by
    funext x
    simp only [map_mul,MvPolynomial.psum,pow_one,map_sum,eval_X,map_pow,pow_one]
    simp only [Finset.expect,NNRat.smul_def,card_univ,Fintype.card_fin,
      NNRat.cast_inv,NNRat.cast_natCast,smul_eq_mul]
    field_simp [hm]
    <;> ring
  unfold singleBaseExpectation
  rw [he,integral_const_mul,mul_div_assoc]
  change (M : ℝ)^2*singleWMoment M 1 = _
  rw [singleWMoment_one hM]
  field_simp [hm]
  <;> ring
private noncomputable def baseMap {M : ℕ} (hM : 1≤M) : MvPolynomial (Fin M ⊕ Fin M) ℝ →ₗ[ℝ] ℝ where
  toFun := baseExpectation M
  map_add' := baseExpectation_add hM
  map_smul' c P := by
    unfold baseExpectation
    simp only [smul_eq_C_mul,map_mul,eval_C,smul_eq_mul,RingHom.id_apply]
    rw [show (fun p : (Fin M → ℝ) × (Fin M → ℝ) => baseWeight M M p*(c*eval (Sum.elim p.1 p.2) P)) =
      (fun p => c*(baseWeight M M p*eval (Sum.elim p.1 p.2) P)) by funext p; ring,
      integral_const_mul]
    ring
private theorem baseMap_C_mul {M : ℕ} (hM : 1≤M) (c : ℝ) (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    baseMap hM (C c*P) = c*baseMap hM P := by
  simpa only [smul_eq_C_mul,smul_eq_mul] using (baseMap hM).map_smul c P
private theorem baseMap_tensor {M : ℕ} (hM : 1≤M) (P Q : MvPolynomial (Fin M) ℝ) :
    baseMap hM (rename Sum.inl P*rename Sum.inr Q) = singleBaseExpectation M P*singleBaseExpectation M Q := by
  exact baseExpectation_tensor hM P Q
private theorem baseMap_left {M : ℕ} (hM : 1≤M) (P : MvPolynomial (Fin M) ℝ) :
    baseMap hM (rename Sum.inl P) = singleBaseExpectation M P := by
  simpa [singleBaseExpectation_one hM] using baseMap_tensor hM P 1
private theorem baseMap_right {M : ℕ} (hM : 1≤M) (P : MvPolynomial (Fin M) ℝ) :
    baseMap hM (rename Sum.inr P) = singleBaseExpectation M P := by
  simpa [singleBaseExpectation_one hM] using baseMap_tensor hM 1 P
private theorem linearDensityPoly_rename (M : ℕ) : linearDensityPoly M =
    C (M : ℝ)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))-rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1))) := by
  simp [linearDensityPoly,MvPolynomial.psum,map_sum]
private theorem quadraticDensityPoly_rename (M : ℕ) : quadraticDensityPoly M =
    C ((M : ℝ)^2/2)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)^2)+rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1)^2))+
    (C 1-C ((M : ℝ)^2))*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1)))-
    C ((M : ℝ)/2)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2))+rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 2))) := by
  simp only [quadraticDensityPoly,linearDensityPoly_rename,MvPolynomial.psum,pow_one,map_sum,map_pow,rename_X]
  have hhalf : (2 : MvPolynomial (Fin M ⊕ Fin M) ℝ)*C (1/2 : ℝ)=1 := by
    calc
      _ = C ((2 : ℝ)*(1/2 : ℝ)) := by rw [map_mul,map_ofNat]
      _ = _ := by norm_num
  simp only [div_eq_mul_inv,map_mul,map_pow,map_one,map_ofNat] at *
  linear_combination ((1-C (M : ℝ)^2)*(∑ i : Fin M, X (Sum.inl i))*(∑ j : Fin M, X (Sum.inr j)))*hhalf
private theorem baseExpectation_density_two {M : ℕ} (hM : 1≤M) :
    baseExpectation M (quadraticDensityPoly M) = 0 := by
  change baseMap hM _ = _
  rw [quadraticDensityPoly_rename]
  simp only [sub_mul,one_mul,map_one,map_sub,map_add,baseMap_C_mul,baseMap_left,baseMap_right,baseMap_tensor,
    singleBaseExpectation_a_sq hM,singleBaseExpectation_a hM,singleBaseExpectation_t hM]
  ring
private theorem a_quadraticDensityPoly_rename (M : ℕ) :
    rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*quadraticDensityPoly M =
      C ((M : ℝ)^2/2)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)^3)+
        rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1)^2))+
      (C 1-C ((M : ℝ)^2))*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)^2)*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1)))-
      C ((M : ℝ)/2)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)*(MvPolynomial.psum (Fin M) ℝ 2))+
        rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 2))) := by
  rw [quadraticDensityPoly_rename]
  simp only [map_pow,map_mul]
  ring
private theorem baseExpectation_a_density_two {M : ℕ} (hM : 1≤M) :
    baseExpectation M (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*quadraticDensityPoly M) = 0 := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  change baseMap hM _ = _
  rw [a_quadraticDensityPoly_rename]
  simp only [sub_mul,one_mul,map_one,map_sub,map_add,baseMap_C_mul,baseMap_left,baseMap_tensor,
    singleBaseExpectation_a_cube hM,singleBaseExpectation_a_sq hM,singleBaseExpectation_a hM,
    singleBaseExpectation_t hM,singleBaseExpectation_at hM]
  field_simp [hm]
  <;> ring
private theorem baseExpectation_t_density_one {M : ℕ} (hM : 1≤M) :
    baseExpectation M (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2))*linearDensityPoly M) = 4*(M : ℝ) := by
  have he : rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2))*linearDensityPoly M =
      C (M : ℝ)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)*(MvPolynomial.psum (Fin M) ℝ 2))-rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2))*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1))) := by
    rw [linearDensityPoly_rename]
    simp only [map_mul]
    ring
  change baseMap hM _ = _
  rw [he,baseMap_C_mul,map_sub,baseMap_left,baseMap_tensor,
    singleBaseExpectation_at hM,singleBaseExpectation_a hM,singleBaseExpectation_t hM]
  ring

private theorem correctionJet_one {d : ℝ} (hd : d ≠ 0) :
    correctionJet (gammaCGF d) (correctionCGF d) 1 = -1 := by
  have h := correction_jet_recurrence (gammaCGF_analytic d) (correctionCGF_analytic d)
    (by simp [gammaCGF]) (by simp [correctionCGF]) 0
  rw [correctionCGF_iterated hd (by norm_num : 1 ≤ 1)] at h
  norm_num at h
  exact h.symm
private theorem rescaled_first_moment {M : ℕ} (hM : 1 ≤ M) :
    FirstOrder (fun γ => ∫ p, rescaledObservable M γ p ∂law M γ) 1 (-1) := by
  have hd : (M : ℝ)^2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM))
  have h := rescaledMomentExpansion M hM 1
  rw [expJet_one hd, correctionJet_one hd] at h
  simpa [ProbabilityTheory.moment] using h
private theorem rescaled_second_moment {M : ℕ} (hM : 1 ≤ M) :
    FirstOrder (fun γ => ∫ p, rescaledObservable M γ p ^ 2 ∂law M γ)
      (1 + ((M : ℝ)^2)⁻¹)
      (correctionJet (gammaCGF ((M : ℝ)^2)) (correctionCGF ((M : ℝ)^2)) 2) := by
  have hd : (M : ℝ)^2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM))
  have h := rescaledMomentExpansion M hM 2
  rw [expJet_two hd] at h
  exact h
private theorem rescaled_moments_bounded {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    (fun γ => ∫ p, rescaledObservable M γ p ^ r ∂law M γ) =O[atTop] (fun _ => (1 : ℝ)) := by
  exact (rescaledMomentExpansion M hM r).tendsto.isBigO_one ℝ
private theorem inv_pow_bigO {a b : ℕ} (h : a ≤ b) :
    (fun γ : ℝ => γ⁻¹^b) =O[atTop] (fun γ : ℝ => γ⁻¹^a) := by
  have hp := (isBigO_pow_pow_cobounded_of_le (R := ℝ) h).mono
    IsOrderBornology.atTop_le_cobounded
  have hz : ∀ᶠ γ : ℝ in atTop, γ ^ a = 0 → γ ^ b = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ ha
    exact (pow_ne_zero _ hγ.ne' ha).elim
  simpa only [inv_pow] using hp.inv_rev hz
private theorem FirstOrder.sub_const_bigO {f : ℝ → ℝ} {a b : ℝ} (h : FirstOrder f a b) :
    (fun γ => f γ-a) =O[atTop] (fun γ : ℝ => γ⁻¹) := by
  have h0 : (fun γ => f γ-a-b*γ⁻¹) =O[atTop] (fun γ : ℝ => γ⁻¹) := by
    simpa only [pow_one] using h.trans (inv_pow_bigO (show 1 ≤ 2 by omega))
  have h1 := (isBigO_refl (fun γ : ℝ => γ⁻¹) atTop).const_mul_left b
  have hh := h0.add h1
  convert hh using 1 <;> ext γ <;> ring
private theorem bounded_times_inv_power {f : ℝ → ℝ} (h : f =O[atTop] (fun _ => (1 : ℝ)))
    {r k : ℕ} (hr : k ≤ r) :
    (fun γ => (-γ⁻¹)^r*f γ) =O[atTop] (fun γ : ℝ => γ⁻¹^k) := by
  have hp := (inv_pow_bigO hr).const_mul_left ((-1 : ℝ)^r)
  have hh := hp.mul h
  convert hh using 1 <;> ext γ <;> (try simp only [neg_pow,mul_one]) <;> ring
private theorem finite_binomial_second_order (m : ℕ → ℝ → ℝ) (a b : ℝ)
    (hm0 : ∀ᶠ γ : ℝ in atTop, m 0 γ = 1)
    (hm1 : FirstOrder (m 1) 1 (-1))
    (hm2 : FirstOrder (m 2) a b)
    (hmb : ∀ r, (m r) =O[atTop] (fun _ => (1 : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    (fun γ : ℝ => (∑ i ∈ range (n+1), (n.choose i : ℝ)*(-γ⁻¹)^i*m i γ) -
       (1-(n : ℝ)*γ⁻¹+((n : ℝ)+(n.choose 2 : ℝ)*a)*γ⁻¹^2))
      =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  have h1 := ((isBigO_refl (fun γ : ℝ => γ⁻¹) atTop).mul hm1).const_mul_left (-(n : ℝ))
  have h1' : (fun γ => -(n : ℝ)*γ⁻¹*(m 1 γ-1+γ⁻¹)) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    convert h1 using 1 <;> ext γ <;> ring
  by_cases hn1 : n = 1
  · subst n
    refine h1'.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm0] with γ hzero
    simp only [show 1+1=2 by omega, sum_range_succ, sum_range_zero, add_zero,
      Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, Nat.choose_eq_zero_of_lt (by omega : 1<2),
      Nat.cast_zero, zero_mul, pow_zero, pow_one, one_mul, hzero]
    ring
  · have hn2 : 2 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn (Ne.symm hn1))
    have h2 := ((isBigO_refl (fun γ : ℝ => γ⁻¹^2) atTop).mul (FirstOrder.sub_const_bigO hm2)).const_mul_left (n.choose 2 : ℝ)
    have h2' : (fun γ => (n.choose 2 : ℝ)*γ⁻¹^2*(m 2 γ-a)) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
      convert h2 using 1 <;> ext γ <;> ring
    have ht : (fun γ => ∑ i ∈ range (n-2), (n.choose (3+i) : ℝ)*(-γ⁻¹)^(3+i)*m (3+i) γ)
        =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
      apply IsBigO.fun_sum
      intro i _
      simpa only [mul_assoc] using
        (bounded_times_inv_power (hmb (3+i)) (show 3 ≤ 3+i by omega)).const_mul_left (n.choose (3+i) : ℝ)
    have hh := (h1'.add h2').add ht
    refine hh.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm0] with γ hzero
    rw [show n+1 = 3+(n-2) by omega, sum_range_add]
    simp only [show (3 : ℕ)=2+1 by omega, sum_range_succ, sum_range_zero, add_zero,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, pow_one,
      one_mul, hzero, neg_sq]
    ring
private theorem tauW_moment_binomial {M : ℕ} (hM : 1 ≤ M) {γ : ℝ} (hγ : 0<γ) (n : ℕ) :
    (∫ p, tauW M γ p ^ n ∂law M γ) = γ⁻¹^n *
      ∑ i ∈ range (n+1), (n.choose i : ℝ)*(-γ⁻¹)^i*(∫ p, rescaledObservable M γ p^i ∂law M γ) := by
  have he (p : (Fin M → ℝ) × (Fin M → ℝ)) :
      tauW M γ p = γ⁻¹*(1+(-γ⁻¹*rescaledObservable M γ p)) := by
    unfold rescaledObservable
    field_simp [hγ.ne']
    <;> ring
  have hb (p : (Fin M → ℝ) × (Fin M → ℝ)) :
      tauW M γ p ^ n = γ⁻¹^n *
        ∑ i ∈ range (n+1), (n.choose i : ℝ)*(-γ⁻¹)^i*rescaledObservable M γ p^i := by
    rw [he, mul_pow, add_comm, add_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [one_pow, mul_one, mul_pow]
    ring
  simp_rw [hb]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact (rescaled_pow_integrable hM hγ i).const_mul _
private theorem bigO_inv_pow_bound {f : ℝ → ℝ} {k : ℕ}
    (h : f =O[atTop] (fun γ : ℝ => γ⁻¹^k)) :
    ∃ C γ₀ : ℝ, 0<γ₀ ∧ ∀ γ : ℝ, γ₀≤γ → |f γ| ≤ C/γ^k := by
  obtain ⟨C,hC⟩ := h.isBigOWith
  obtain ⟨G,hG⟩ := Filter.eventually_atTop.mp hC.bound
  refine ⟨C,max G 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro γ hγ
  have hpos : 0<γ := lt_of_lt_of_le zero_lt_one ((le_max_right G 1).trans hγ)
  have hh := hG γ ((le_max_left G 1).trans hγ)
  simpa only [Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hpos,div_eq_mul_inv,inv_pow] using hh
private theorem wigner_normalized_second_order {M : ℕ} (hM : 1≤M) (n : ℕ) (hn : 1≤n) :
    (fun γ : ℝ =>
      (∑ i ∈ range (n+1), (n.choose i : ℝ)*(-γ⁻¹)^i*(∫ p, rescaledObservable M γ p^i ∂law M γ))-
      (1-(n : ℝ)*γ⁻¹ + (n*((n+1)*(M : ℝ)^2+(n-1))/(2*(M : ℝ)^2))*γ⁻¹^2))
       =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  have hzero : ∀ᶠ γ : ℝ in atTop, (∫ p, rescaledObservable M γ p^0 ∂law M γ) = 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    letI := law_isProbability hM (lt_of_lt_of_le zero_lt_one hγ)
    simp
  have h := finite_binomial_second_order
    (fun i γ => ∫ p, rescaledObservable M γ p^i ∂law M γ)
    (1+((M : ℝ)^2)⁻¹) _ hzero (by simpa only [pow_one] using rescaled_first_moment hM)
    (rescaled_second_moment hM) (rescaled_moments_bounded hM) n hn
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  have hc : (n : ℝ)+(n.choose 2 : ℝ)*(1+((M : ℝ)^2)⁻¹) =
      (n*((n+1)*(M : ℝ)^2+(n-1))/(2*(M : ℝ)^2)) := by
    rw [Nat.cast_choose_two]
    field_simp [hm]
    ring
  rwa [hc] at h
private theorem result55 : claim55 := by
  intro M hM n hn
  have h := (isBigO_refl (fun γ : ℝ => γ⁻¹^n) atTop).mul (wigner_normalized_second_order hM n hn)
  have hh : (fun γ =>
      (∫ p, tauW M γ p^n ∂law M γ)-
      (1/γ^n-n/γ^(n+1)+(n*((n+1)*(M : ℝ)^2+(n-1)))/(2*(M : ℝ)^2*γ^(n+2))))
       =O[atTop] (fun γ : ℝ => γ⁻¹^(n+3)) := by
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
      have hpos : 0<γ := lt_of_lt_of_le zero_lt_one hγ
      rw [tauW_moment_binomial hM hpos n]
      simp only [pow_add, pow_one, inv_pow, mul_inv_rev, div_eq_mul_inv]
      ring
    · exact Filter.Eventually.of_forall (fun γ => by ring)
  exact bigO_inv_pow_bound hh
private theorem rescaled_delay_bounds {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ x/(1+t*x) ∧ x/(1+t*x) ≤ x := by
  have hd : 0 < 1+t*x := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hx)
  constructor
  · exact div_nonneg hx hd.le
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg ht (sq_nonneg x)]
private theorem rescaled_delay_linear_error {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    x-x/(1+t*x) ≤ t*x^2 := by
  have hd : 0 < 1+t*x := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hx)
  have he : x-x/(1+t*x) = t*x^2/(1+t*x) := by field_simp [hd.ne']; ring
  rw [he]
  exact div_le_self (by positivity) (by nlinarith [mul_nonneg ht hx])
private theorem rescaled_delay_cubic_remainder {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    |x/(1+t*x)-x+t*x^2-t^2*x^3| ≤ t^3*x^4 := by
  have hd : 0 < 1+t*x := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hx)
  have he : x/(1+t*x)-x+t*x^2-t^2*x^3 = -(t^3*x^4/(1+t*x)) := by field_simp [hd.ne']; ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) (by nlinarith [mul_nonneg ht hx])
private theorem rescaled_delay_square_remainder {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    |(x/(1+t*x))^2-x^2+2*t*x^3| ≤ 3*t^2*x^4 := by
  have hd : 0 < 1+t*x := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hx)
  have he : (x/(1+t*x))^2-x^2+2*t*x^3 = t^2*x^4*((3+2*t*x)/(1+t*x)^2) := by
    field_simp [hd.ne']
    ring
  rw [he, abs_of_nonneg (by positivity)]
  have hb : (3+2*t*x)/(1+t*x)^2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [sq_nonneg (t*x),mul_nonneg ht hx]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ t^2*x^4 by positivity)
  nlinarith [hh]
private theorem rescaled_delay_cube_remainder {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    |(x/(1+t*x))^3-x^3| ≤ 3*t*x^4 := by
  let u := x/(1+t*x)
  obtain ⟨hu0,hux⟩ := rescaled_delay_bounds ht hx
  have he : x^3-u^3 = (x-u)*(x^2+x*u+u^2) := by ring
  have h1 : x-u ≤ t*x^2 := rescaled_delay_linear_error ht hx
  have h2 : x^2+x*u+u^2 ≤ 3*x^2 := by
    have hm := mul_le_mul_of_nonneg_left hux hx
    have hs := pow_le_pow_left₀ hu0 hux 2
    nlinarith
  have h3 : u^3 ≤ x^3 := pow_le_pow_left₀ hu0 hux 3
  change |u^3-x^3| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr h3)]
  have hh := mul_le_mul h1 h2 (show 0 ≤ x^2+x*u+u^2 by positivity) (by positivity : 0 ≤ t*x^2)
  rw [← he] at hh
  nlinarith [hh]
private noncomputable def spectralPoly (M r : ℕ) : MvPolynomial (Fin M ⊕ Fin M) ℝ :=
  C ((M : ℝ)⁻¹)*rename Sum.inl (MvPolynomial.psum (Fin M) ℝ r)
private noncomputable def spectralRescaled (M r : ℕ) (γ : ℝ) (p : (Fin M → ℝ) × (Fin M → ℝ)) : ℝ :=
  (M : ℝ)⁻¹*powerSum M r (fun i => p.1 i/(1+γ⁻¹*p.1 i))
private theorem spectralPoly_eval (M r : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) (spectralPoly M r) = (M : ℝ)⁻¹*∑ i, (p.1 i)^r := by
  simp [spectralPoly,MvPolynomial.psum,map_sum]
private theorem baseExpectation_a_density_one {M : ℕ} (hM : 1≤M) :
    baseExpectation M (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*linearDensityPoly M) = (M : ℝ) := by
  have he : rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*linearDensityPoly M =
      C (M : ℝ)*(rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)^2)-rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*rename Sum.inr ((MvPolynomial.psum (Fin M) ℝ 1))) := by
    rw [linearDensityPoly_rename]
    simp only [map_pow]
    ring
  change baseMap hM _ = _
  rw [he,baseMap_C_mul,map_sub,baseMap_left,baseMap_tensor,
    singleBaseExpectation_a_sq hM,singleBaseExpectation_a hM]
  ring
private theorem baseExpectation_spectral_low {M : ℕ} (hM : 1≤M) :
    baseExpectation M (spectralPoly M 1)=1 ∧
    baseExpectation M (spectralPoly M 2)=2 ∧
    baseExpectation M (spectralPoly M 3)=5+((M : ℝ)^2)⁻¹ ∧
    baseExpectation M (spectralPoly M 1*linearDensityPoly M)=1 ∧
    baseExpectation M (spectralPoly M 1*quadraticDensityPoly M)=0 ∧
    baseExpectation M (spectralPoly M 2*linearDensityPoly M)=4 := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  have h1 : spectralPoly M 1=C ((M : ℝ)⁻¹)*rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1)) := by simp [spectralPoly,MvPolynomial.psum]
  have h2 : spectralPoly M 2=C ((M : ℝ)⁻¹)*rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2)) := rfl
  have h3 : spectralPoly M 3=C ((M : ℝ)⁻¹)*rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 3)) := rfl
  have hE : ∀ P, baseExpectation M P=baseMap hM P := fun _ => rfl
  simp only [h1,h2,h3,hE,mul_assoc,baseMap_C_mul,baseMap_left,
    singleBaseExpectation_a hM,singleBaseExpectation_t hM,singleBaseExpectation_c hM,
    show baseMap hM (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*linearDensityPoly M)=M from baseExpectation_a_density_one hM,
    show baseMap hM (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 1))*quadraticDensityPoly M)=0 from baseExpectation_a_density_two hM,
    show baseMap hM (rename Sum.inl ((MvPolynomial.psum (Fin M) ℝ 2))*linearDensityPoly M)=4*(M : ℝ) from baseExpectation_t_density_one hM]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp <;> ring
  constructor
  · field_simp
  constructor
  · ring
  · field_simp
private theorem law_spectral_one_second {M : ℕ} (hM : 1≤M) :
    (fun γ => (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 1) ∂law M γ)-1-γ⁻¹)
      =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  have hm : (M : ℝ)>0 := Nat.cast_pos'.mpr hM
  have hz : (partition M M)^2≠0 := pow_ne_zero _ (partition_pos M hm).ne'
  have hD := baseExpectation_density_two hM
  unfold baseExpectation at hD
  have hD' : (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (quadraticDensityPoly M))=0 :=
    (div_eq_zero_iff).mp hD |>.resolve_right hz
  have h := law_polynomial_secondOrder hM hD' (spectralPoly M 1)
  change (fun γ => (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 1) ∂law M γ)-
    baseExpectation M (spectralPoly M 1)-γ⁻¹*baseExpectation M (spectralPoly M 1*linearDensityPoly M)-
    γ⁻¹^2*baseExpectation M (spectralPoly M 1*quadraticDensityPoly M)) =O[atTop] _ at h
  rcases baseExpectation_spectral_low hM with ⟨h1,_,_,hD1,hD2,_⟩
  simpa only [h1,hD1,hD2,mul_one,mul_zero,sub_zero] using h
private theorem law_spectral_two_first {M : ℕ} (hM : 1≤M) :
    FirstOrder (fun γ => ∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 2) ∂law M γ) 2 4 := by
  have h := law_polynomial_firstOrder hM (spectralPoly M 2)
  rcases baseExpectation_spectral_low hM with ⟨_,h2,_,_,_,hD⟩
  change FirstOrder _ (baseExpectation M (spectralPoly M 2))
    (baseExpectation M (spectralPoly M 2*linearDensityPoly M)) at h
  rwa [h2,hD] at h
private theorem law_spectral_three_first {M : ℕ} (hM : 1≤M) :
    FirstOrder (fun γ => ∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ)
      (5+((M : ℝ)^2)⁻¹) (baseExpectation M (spectralPoly M 3*linearDensityPoly M)) := by
  have h := law_polynomial_firstOrder hM (spectralPoly M 3)
  have h3 := (baseExpectation_spectral_low hM).2.2.1
  change FirstOrder _ (baseExpectation M (spectralPoly M 3)) _ at h
  rwa [h3] at h
private theorem law_remainder_power {M : ℕ} (hM : 1≤M)
    (f : ℝ → (Fin M → ℝ) × (Fin M → ℝ) → ℝ)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) (k : ℕ)
    (hbound : ∀ γ : ℝ, 1≤γ → ∀ p, p∈supportSet M γ →
      |f γ p|≤γ⁻¹^k*eval (Sum.elim p.1 p.2) P) :
    (fun γ => ∫ p, f γ p ∂law M γ) =O[atTop] (fun γ : ℝ => γ⁻¹^k) := by
  have hE := (law_polynomial_firstOrder hM P).tendsto
  have hEB : (fun γ => ∫ p, eval (Sum.elim p.1 p.2) P ∂law M γ) =O[atTop] (fun _ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hE one_ne_zero
  obtain ⟨C,hC⟩ := hEB.bound
  apply IsBigO.of_bound C
  filter_upwards [hC,eventually_ge_atTop (1 : ℝ)] with γ hc hγ
  have hpos := lt_of_lt_of_le zero_lt_one hγ
  have ht : 0≤γ⁻¹ := inv_nonneg.mpr hpos.le
  have hb : ∀ᵐ p ∂law M γ, ‖f γ p‖ ≤ γ⁻¹^k*eval (Sum.elim p.1 p.2) P := by
    filter_upwards [law_ae_support M γ] with p hp
    simpa only [Real.norm_eq_abs] using hbound γ hγ p hp
  have hi := norm_integral_le_of_norm_le ((law_polynomial_integrable hM hpos P).const_mul (γ⁻¹^k)) hb
  rw [integral_const_mul] at hi
  have hh := (le_abs_self (∫ p, eval (Sum.elim p.1 p.2) P ∂law M γ)).trans
    (by simpa only [Real.norm_eq_abs,norm_one,mul_one] using hc)
  have hfinal := hi.trans (mul_le_mul_of_nonneg_left hh (pow_nonneg ht k))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht k),mul_comm] using hfinal
private theorem spectralRescaled_bounds {M r : ℕ} {γ : ℝ} (hγ : 0<γ)
    (p : (Fin M → ℝ) × (Fin M → ℝ)) (hp : p∈supportSet M γ) :
    0≤spectralRescaled M r γ p ∧
      spectralRescaled M r γ p≤eval (Sum.elim p.1 p.2) (spectralPoly M r) := by
  have hx : ∀ i, 0≤p.1 i := ((supportSet_membership M γ p).mp hp).1
  have ht := inv_nonneg.mpr hγ.le
  have h0 (i : Fin M) := rescaled_delay_bounds ht (hx i)
  constructor
  · unfold spectralRescaled
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => pow_nonneg (h0 i).1 r)
  · rw [spectralRescaled,powerSum,spectralPoly_eval]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (h0 i).1 (h0 i).2 r
private theorem spectralRescaled_integrable {M : ℕ} (hM : 1≤M) {γ : ℝ} (hγ : 0<γ) (r : ℕ) :
    Integrable (spectralRescaled M r γ) (law M γ) := by
  apply (law_polynomial_integrable hM hγ (spectralPoly M r)).mono'
  · exact (by unfold spectralRescaled powerSum; fun_prop : Measurable (spectralRescaled M r γ)).aestronglyMeasurable
  · filter_upwards [law_ae_support M γ] with p hp
    obtain ⟨h0,h1⟩ := spectralRescaled_bounds hγ p hp
    rw [Real.norm_eq_abs,abs_of_nonneg h0]
    exact h1
private theorem spectralRescaled_moments_bounded {M : ℕ} (hM : 1≤M) (r : ℕ) :
    (fun γ => ∫ p, spectralRescaled M r γ p ∂law M γ) =O[atTop] (fun _ => (1 : ℝ)) := by
  have h := law_remainder_power hM (spectralRescaled M r) (spectralPoly M r) 0 (by
    intro γ hγ p hp
    obtain ⟨h0,h1⟩ := spectralRescaled_bounds (lt_of_lt_of_le zero_lt_one hγ) p hp
    rw [pow_zero,one_mul,abs_of_nonneg h0]
    exact h1)
  simpa only [pow_zero] using h
private theorem average_abs_bound {M : ℕ} (f g : Fin M → ℝ) (h : ∀ i, |f i|≤g i) :
    |(M : ℝ)⁻¹*∑ i, f i|≤(M : ℝ)⁻¹*∑ i, g i := by
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(M : ℝ)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => h i))
private theorem spectralRescaled_jet_bounds {M : ℕ} {γ : ℝ} (hγ : 0<γ)
    (p : (Fin M → ℝ) × (Fin M → ℝ)) (hp : p∈supportSet M γ) :
    |spectralRescaled M 1 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 1)+
      γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 2)-
      γ⁻¹^2*eval (Sum.elim p.1 p.2) (spectralPoly M 3)| ≤
        γ⁻¹^3*eval (Sum.elim p.1 p.2) (spectralPoly M 4) ∧
    |spectralRescaled M 2 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 2)+
      2*γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 3)| ≤
        γ⁻¹^2*eval (Sum.elim p.1 p.2) (C 3*spectralPoly M 4) ∧
    |spectralRescaled M 3 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 3)| ≤
        γ⁻¹*eval (Sum.elim p.1 p.2) (C 3*spectralPoly M 4) := by
  have hx : ∀ i, 0≤p.1 i := ((supportSet_membership M γ p).mp hp).1
  have ht : 0≤γ⁻¹ := inv_nonneg.mpr hγ.le
  have h1 := average_abs_bound
    (fun i => p.1 i/(1+γ⁻¹*p.1 i)-p.1 i+γ⁻¹*(p.1 i)^2-γ⁻¹^2*(p.1 i)^3)
    (fun i => γ⁻¹^3*(p.1 i)^4) (fun i => rescaled_delay_cubic_remainder ht (hx i))
  have h2 := average_abs_bound
    (fun i => (p.1 i/(1+γ⁻¹*p.1 i))^2-(p.1 i)^2+2*γ⁻¹*(p.1 i)^3)
    (fun i => 3*γ⁻¹^2*(p.1 i)^4) (fun i => rescaled_delay_square_remainder ht (hx i))
  have h3 := average_abs_bound
    (fun i => (p.1 i/(1+γ⁻¹*p.1 i))^3-(p.1 i)^3)
    (fun i => 3*γ⁻¹*(p.1 i)^4) (fun i => rescaled_delay_cube_remainder ht (hx i))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at h1 h2 h3
  simp only [spectralRescaled,powerSum,spectralPoly_eval,map_mul,eval_C,pow_one]
  constructor
  · convert h1 using 1
    · congr 1; ring
    · ring
  constructor
  · convert h2 using 1
    · congr 1; ring
    · ring
  · convert h3 using 1
    · congr 1; ring
    · ring
private theorem spectralRescaled_integral_jets {M : ℕ} (hM : 1≤M) :
    (fun γ => (∫ p, spectralRescaled M 1 γ p ∂law M γ)-
      (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 1) ∂law M γ)+
      γ⁻¹*(∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 2) ∂law M γ)-
      γ⁻¹^2*(∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ))
      =O[atTop] (fun γ : ℝ => γ⁻¹^3) ∧
    (fun γ => (∫ p, spectralRescaled M 2 γ p ∂law M γ)-
      (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 2) ∂law M γ)+
      2*γ⁻¹*(∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ))
      =O[atTop] (fun γ : ℝ => γ⁻¹^2) ∧
    (fun γ => (∫ p, spectralRescaled M 3 γ p ∂law M γ)-
      (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ))
      =O[atTop] (fun γ : ℝ => γ⁻¹) := by
  have h1 := law_remainder_power hM
    (fun γ p => spectralRescaled M 1 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 1)+
      γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 2)-γ⁻¹^2*eval (Sum.elim p.1 p.2) (spectralPoly M 3))
    (spectralPoly M 4) 3 (by
      intro γ hγ p hp
      exact (spectralRescaled_jet_bounds (lt_of_lt_of_le zero_lt_one hγ) p hp).1)
  have h2 := law_remainder_power hM
    (fun γ p => spectralRescaled M 2 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 2)+
      2*γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 3))
    (C 3*spectralPoly M 4) 2 (by
      intro γ hγ p hp
      exact (spectralRescaled_jet_bounds (lt_of_lt_of_le zero_lt_one hγ) p hp).2.1)
  have h3 := law_remainder_power hM
    (fun γ p => spectralRescaled M 3 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 3))
    (C 3*spectralPoly M 4) 1 (by
      intro γ hγ p hp
      simpa only [pow_one] using (spectralRescaled_jet_bounds (lt_of_lt_of_le zero_lt_one hγ) p hp).2.2)
  have he1 : ∀ᶠ γ : ℝ in atTop,
      (∫ p, spectralRescaled M 1 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 1)+
        γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 2)-γ⁻¹^2*eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ) =
      (∫ p, spectralRescaled M 1 γ p ∂law M γ)-
        (∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 1) ∂law M γ)+
        γ⁻¹*(∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 2) ∂law M γ)-
        γ⁻¹^2*(∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    have hpos := lt_of_lt_of_le zero_lt_one hγ
    have hi (r) := law_polynomial_integrable hM hpos (spectralPoly M r)
    rw [integral_sub (f := fun p => spectralRescaled M 1 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 1)+γ⁻¹*eval (Sum.elim p.1 p.2) (spectralPoly M 2)) (((spectralRescaled_integrable hM hpos 1).sub (hi 1)).add ((hi 2).const_mul γ⁻¹)) ((hi 3).const_mul (γ⁻¹^2)),
      integral_add (f := fun p => spectralRescaled M 1 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 1)) ((spectralRescaled_integrable hM hpos 1).sub (hi 1)) ((hi 2).const_mul γ⁻¹),
      integral_sub (spectralRescaled_integrable hM hpos 1) (hi 1),integral_const_mul,integral_const_mul]
  constructor
  · exact h1.congr' he1 Filter.EventuallyEq.rfl
  constructor
  · refine h2.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    have hpos := lt_of_lt_of_le zero_lt_one hγ
    have hi (r) := law_polynomial_integrable hM hpos (spectralPoly M r)
    rw [integral_add (f := fun p => spectralRescaled M 2 γ p-eval (Sum.elim p.1 p.2) (spectralPoly M 2)) ((spectralRescaled_integrable hM hpos 2).sub (hi 2)) ((hi 3).const_mul (2*γ⁻¹)),
      integral_sub (spectralRescaled_integrable hM hpos 2) (hi 2),integral_const_mul]
  · simp only [pow_one] at h3
    refine h3.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    have hpos := lt_of_lt_of_le zero_lt_one hγ
    rw [integral_sub (spectralRescaled_integrable hM hpos 3) (law_polynomial_integrable hM hpos (spectralPoly M 3))]
private theorem cast_choose_three (n : ℕ) :
    (n.choose 3 : ℝ) = (n : ℝ)*((n : ℝ)-1)*((n : ℝ)-2)/6 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  norm_num [descPochhammer_succ_eval, descPochhammer_zero, Nat.factorial_succ] <;> ring
private theorem finite_binomial_third_order (m : ℕ → ℝ → ℝ) (a b c : ℝ)
    (hm0 : ∀ᶠ γ : ℝ in atTop, m 0 γ=1)
    (hm1 : (fun γ => m 1 γ-1+γ⁻¹-a*γ⁻¹^2) =O[atTop] (fun γ : ℝ => γ⁻¹^3))
    (hm2 : FirstOrder (m 2) 2 b)
    (hm3 : (fun γ => m 3 γ-c) =O[atTop] (fun γ : ℝ => γ⁻¹))
    (hmb : ∀ r, m r =O[atTop] (fun _ => (1 : ℝ))) (n : ℕ) (hn : 1≤n) :
    (fun γ => (∑ i ∈ range (n+1), (n.choose i : ℝ)*(-γ⁻¹)^i*m i γ)-
      (1-(n : ℝ)*γ⁻¹+(n : ℝ)^2*γ⁻¹^2+
       (-(n : ℝ)*a+(n.choose 2 : ℝ)*b-(n.choose 3 : ℝ)*c)*γ⁻¹^3))
       =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
  have h1 := ((isBigO_refl (fun γ : ℝ => γ⁻¹) atTop).mul hm1).const_mul_left (-(n : ℝ))
  have h1' : (fun γ => -(n : ℝ)*γ⁻¹*(m 1 γ-1+γ⁻¹-a*γ⁻¹^2)) =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
    convert h1 using 1 <;> ext γ <;> ring
  have h2 := ((isBigO_refl (fun γ : ℝ => γ⁻¹^2) atTop).mul hm2).const_mul_left (n.choose 2 : ℝ)
  have h2' : (fun γ => (n.choose 2 : ℝ)*γ⁻¹^2*(m 2 γ-2-b*γ⁻¹)) =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
    convert h2 using 1 <;> ext γ <;> ring
  have h3 := ((isBigO_refl (fun γ : ℝ => γ⁻¹^3) atTop).mul hm3).const_mul_left (-(n.choose 3 : ℝ))
  have h3' : (fun γ => -(n.choose 3 : ℝ)*γ⁻¹^3*(m 3 γ-c)) =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
    convert h3 using 1 <;> ext γ <;> ring
  by_cases hn1 : n=1
  · subst n
    refine h1'.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm0] with γ hzero
    norm_num [sum_range_succ,hzero,cast_choose_three]
    ring
  by_cases hn2 : n=2
  · subst n
    have h := h1'.add h2'
    refine h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm0] with γ hzero
    norm_num [sum_range_succ,hzero,cast_choose_three]
    ring
  · have hn3 : 3≤n := Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt (lt_of_le_of_ne hn (Ne.symm hn1))) (Ne.symm hn2))
    have ht : (fun γ => ∑ i ∈ range (n-3), (n.choose (4+i) : ℝ)*(-γ⁻¹)^(4+i)*m (4+i) γ)
        =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
      apply IsBigO.fun_sum
      intro i _
      simpa only [mul_assoc] using (bounded_times_inv_power (hmb (4+i))
        (show 4≤4+i by omega)).const_mul_left (n.choose (4+i) : ℝ)
    have h := ((h1'.add h2').add h3').add ht
    refine h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm0] with γ hzero
    rw [show n+1=4+(n-3) by omega,sum_range_add]
    simp only [show (4 : ℕ)=3+1 by omega,show (3 : ℕ)=2+1 by omega,
      sum_range_succ,sum_range_zero,add_zero,Nat.choose_zero_right,Nat.choose_one_right,
      Nat.cast_one,pow_zero,pow_one,one_mul,hzero,neg_sq,
      show (-γ⁻¹)^3 = -(γ⁻¹^3) by exact (by decide : Odd (3 : ℕ)).neg_pow (γ⁻¹),
      cast_choose_three,Nat.cast_choose_two]
    ring
private theorem spectral_moments_low {M : ℕ} (hM : 1≤M) :
    (fun γ => (∫ p, spectralRescaled M 1 γ p ∂law M γ)-1+γ⁻¹-
      (1+((M : ℝ)^2)⁻¹)*γ⁻¹^2) =O[atTop] (fun γ : ℝ => γ⁻¹^3) ∧
    FirstOrder (fun γ => ∫ p, spectralRescaled M 2 γ p ∂law M γ) 2 (-6-2*((M : ℝ)^2)⁻¹) ∧
    (fun γ => (∫ p, spectralRescaled M 3 γ p ∂law M γ)-(5+((M : ℝ)^2)⁻¹))
      =O[atTop] (fun γ : ℝ => γ⁻¹) := by
  obtain ⟨h1,h2,h3⟩ := spectralRescaled_integral_jets hM
  have hl2 := law_spectral_two_first hM
  have hl3 := FirstOrder.sub_const_bigO (law_spectral_three_first hM)
  have ht2 : (fun γ => γ⁻¹*((∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 2) ∂law M γ)-2-4*γ⁻¹))
      =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    convert (isBigO_refl (fun γ : ℝ => γ⁻¹) atTop).mul hl2 using 1 <;> ext γ <;> ring
  have ht3 : (fun γ => γ⁻¹^2*((∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ)-(5+((M : ℝ)^2)⁻¹)))
      =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    convert (isBigO_refl (fun γ : ℝ => γ⁻¹^2) atTop).mul hl3 using 1 <;> ext γ <;> ring
  constructor
  · have h := ((h1.add (law_spectral_one_second hM)).sub ht2).add ht3
    convert h using 1 <;> ext γ <;> ring
  constructor
  · have ht3' : (fun γ => 2*γ⁻¹*((∫ p, eval (Sum.elim p.1 p.2) (spectralPoly M 3) ∂law M γ)-(5+((M : ℝ)^2)⁻¹)))
        =O[atTop] (fun γ : ℝ => γ⁻¹^2) := by
      convert ((isBigO_refl (fun γ : ℝ => γ⁻¹) atTop).mul hl3).const_mul_left 2 using 1 <;> ext γ <;> ring
    have h := (h2.add hl2).sub ht3'
    unfold FirstOrder
    convert h using 1 <;> ext γ <;> ring
  · have h := h3.add hl3
    convert h using 1 <;> ext γ <;> ring
private theorem traceQPow_moment_binomial {M : ℕ} (hM : 1≤M) {γ : ℝ} (hγ : 0<γ) (n : ℕ) :
    (∫ p, traceQPow M n γ p ∂law M γ) =
      γ⁻¹^n*∑ r ∈ range (n+1), (n.choose r : ℝ)*(-γ⁻¹)^r*
        (∫ p, spectralRescaled M r γ p ∂law M γ) := by
  have hb : ∀ᵐ p ∂law M γ,
      traceQPow M n γ p = γ⁻¹^n*
        ∑ r ∈ range (n+1), (n.choose r : ℝ)*(-γ⁻¹)^r*spectralRescaled M r γ p := by
    filter_upwards [law_ae_support M γ] with p hp
    have hx : ∀ i, 0≤p.1 i := ((supportSet_membership M γ p).mp hp).1
    have hq (i : Fin M) : 1/(γ+p.1 i) = γ⁻¹*(1+(-γ⁻¹)*(p.1 i/(1+γ⁻¹*p.1 i))) := by
      have hxi := hx i
      have ht : 0≤γ⁻¹ := inv_nonneg.mpr hγ.le
      have hd : 0<1+γ⁻¹*p.1 i := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht (hx i))
      have hd' : 0<γ+p.1 i := Right.add_pos_of_pos_of_nonneg hγ (hx i)
      field_simp [hd.ne',hd'.ne',hγ.ne']
      <;> ring
    have hbn (i : Fin M) : (1/(γ+p.1 i))^n = γ⁻¹^n*
        ∑ r ∈ range (n+1), (n.choose r : ℝ)*(-γ⁻¹)^r*(p.1 i/(1+γ⁻¹*p.1 i))^r := by
      rw [hq,mul_pow,add_comm,add_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      simp only [one_pow,mul_one,mul_pow]
      ring
    simp only [traceQPow,hbn,spectralRescaled,powerSum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp only [←Finset.mul_sum]
    ring

  rw [integral_congr_ae hb,integral_const_mul,integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro r _
    exact (spectralRescaled_integrable hM hγ r).const_mul _
private theorem spectral_normalized_third_order {M : ℕ} (hM : 1≤M) (n : ℕ) (hn : 1≤n) :
    (fun γ => (∑ r ∈ range (n+1), (n.choose r : ℝ)*(-γ⁻¹)^r*(∫ p, spectralRescaled M r γ p ∂law M γ))-
      (1-(n : ℝ)*γ⁻¹+(n : ℝ)^2*γ⁻¹^2-
        ((n+1)*(n*(5*n-2)*(M : ℝ)^2+n*(n+2))/(6*(M : ℝ)^2))*γ⁻¹^3))
      =O[atTop] (fun γ : ℝ => γ⁻¹^4) := by
  have hm : (M : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hM)
  have hzero : ∀ᶠ γ : ℝ in atTop, (∫ p, spectralRescaled M 0 γ p ∂law M γ)=1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    letI := law_isProbability hM (lt_of_lt_of_le zero_lt_one hγ)
    have he : spectralRescaled M 0 γ=(fun _ => (1 : ℝ)) := by
      funext p
      simp [spectralRescaled,powerSum,hm]
    rw [he]
    simp
  obtain ⟨h1,h2,h3⟩ := spectral_moments_low hM
  have h := finite_binomial_third_order
    (fun r γ => ∫ p, spectralRescaled M r γ p ∂law M γ)
    (1+((M : ℝ)^2)⁻¹) (-6-2*((M : ℝ)^2)⁻¹) (5+((M : ℝ)^2)⁻¹)
    hzero h1 h2 h3 (spectralRescaled_moments_bounded hM) n hn
  have hc : -(n : ℝ)*(1+((M : ℝ)^2)⁻¹)+(n.choose 2 : ℝ)*(-6-2*((M : ℝ)^2)⁻¹)-
      (n.choose 3 : ℝ)*(5+((M : ℝ)^2)⁻¹) =
      -((n+1)*(n*(5*n-2)*(M : ℝ)^2+n*(n+2))/(6*(M : ℝ)^2)) := by
    rw [Nat.cast_choose_two,cast_choose_three]
    field_simp [hm]
    <;> ring
  rw [hc] at h
  simpa only [neg_mul,sub_eq_add_neg] using h
private theorem result54 : claim54 := by
  intro M hM n hn
  have h := (isBigO_refl (fun γ : ℝ => γ⁻¹^n) atTop).mul (spectral_normalized_third_order hM n hn)
  have hh : (fun γ => (∫ p, traceQPow M n γ p ∂law M γ)-
      (1/γ^n-n/γ^(n+1)+(n : ℝ)^2/γ^(n+2)-
       (n+1)*(n*(5*n-2)*(M : ℝ)^2+n*(n+2))/(6*(M : ℝ)^2*γ^(n+3))))
      =O[atTop] (fun γ : ℝ => γ⁻¹^(n+4)) := by
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
      rw [traceQPow_moment_binomial hM (lt_of_lt_of_le zero_lt_one hγ) n]
      simp only [pow_add,pow_one,inv_pow,mul_inv_rev,div_eq_mul_inv]
      ring
    · exact Filter.Eventually.of_forall (fun γ => by ring)
  exact bigO_inv_pow_bound hh

theorem result : claim := by
  exact ⟨result54,result55⟩

end D5.S3.Quantum.Transport.StrongAbsorptionMoments
