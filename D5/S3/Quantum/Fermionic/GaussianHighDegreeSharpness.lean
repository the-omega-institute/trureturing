/- GID: D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/GaussianHighDegreeSharpness
   mirror-E: none(waiver:quantified-high-degree-sharpness)
   anchors: []
   utility: none
   digest: The fermionic high-degree energy and free-energy constants are sharp. -/

/-
result:
  proof_shape: content
  escape_witness: the coordinate conference family has a joint minus ground sector
    at the universal bound, while every physical product has zero energy.
admission_basis: open-problem-resolution (#13091; Proved)
Same-delivery inlined content: GibbsProductGap, FlatCliffordGround, CoordinateAverage, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Entropy/MaxEntropy.entropy_le_log_card
    statement_id: sha256:2036c3d1e460f61aa9db5be6bee1f085a8eb400f9dccacc5244afc890263d5b5
  GID: D5/S3/Entropy/MaxEntropy.shannonEntropy
    statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
  GID: D5/S3/QuadraticForms/PositiveDefiniteWilliamson.skew_paired_basis_induction
    statement_id: sha256:54436ecddd85ddabca9cde51fd34930a3412b14577a5dd01f02b1f5f542233e1
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbsState
    statement_id: sha256:f892a87bde5011f4627a32ee2080dbc7463d33d90133420b234b8da2d2c4d7da
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity
    statement_id: sha256:895916cae977ded768955734c3e815db72f7049759d4a7a6a6149251df958326
  GID: D5/S3/Quantum/Divergence/GibbsVariationalIdentity.partitionFunction
    statement_id: sha256:0a01d1cd9d793907eb4414251b21f716dd8fe57b344c4e234875502c8938d9a2
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy
    statement_id: sha256:1fde73d469bc7e293eef439b271276205450d8758cb7358eaadae794794d8f0a
  GID: D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy
    statement_id: sha256:9cf1e21822d8f3f61a5d349f41c4287a3ef43a0e8a600534b28ab8d06f437cd1
  GID: D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
    statement_id: sha256:4c9f2eff40b9ab9a5dd6bf3511ef67bd738e5144793aa9213135c3c33bf35942
  GID: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.densityMatrix
    statement_id: sha256:e8ba081c519bb0c785f070157864cb2f6eecf4b55d1e6b6b8c50a07b3fb988a6
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.meanEnergy
    statement_id: sha256:9968a03e56960da489176141fea72cbed63e67cc32e2fe1378c92e3fed11906b
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.thermalState
    statement_id: sha256:c2e22ee34d0f1ca2980b540f9d8f8f13364fa370def51a817c01961207ed18c1
  GID: D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
    statement_id: sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.free_negentropy_budget
    statement_id: sha256:0b886ab8a8eb94b90ce39b027be67936f47de33369529a5679075100a0c83f4b
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.stateSpectrum
    statement_id: sha256:38e1263bbbed60675d6786fa06658d9d5a3c26885815452280ecf9b8fafbd141
  GID: D5/S3/Quantum/Sharpness/FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum
    statement_id: sha256:418a3458d7e30f3b6473c08140a6b2fe6d7de5cfc410395fca6ee760d8ec80bd
  GID: D5/S3/Quantum/Sharpness/SpectralPairingCapacity.spectralPairingCapacity
    statement_id: sha256:d4afa8ecdad28cf3ab52fa0d495db95b1e14c30a3244dbfc4ff876e5b48677b4
  GID: D5/S3/Quantum/Sharpness/SpectralSharpness.spectralSharpness
    statement_id: sha256:297963932869a2d0947ffa0785c89eb0afa76eb964ab29d3f88738daffab84d2
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR
    statement_id: sha256:91a39cca0cc0155aec0a40a8280d10bd356a0d091f81f8031b64299b1ade63de
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt
    statement_id: sha256:1db13273a320d9215f5583b5d1bcd5cf5cff7952171e37a663fc509057aaacd4
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt
    statement_id: sha256:eb93c9ae1da812ac8631c45850a4bd5f0d160da82cbfe9ad9d4377f14362f664
  GID: D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder.positiveBiasLaw
    statement_id: sha256:473a802511d0e55f9584e9c1920f5e9c930ab5cc45d69cab1814325c649297b6
  GID: D5/S3/TotalVariation/Pinsker.totalVariation
    statement_id: sha256:417383b2f5f4a4f7c56881e521c516e431c6f287d2d24996ca4ec3797e2e61f3
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
  GID: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
    statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
computational_content.kind: none; quantification is uniform over modes and degree cutoffs.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Fermionic.GibbsProductGap
import D5.S3.Quantum.Fermionic.FlatCliffordGround
import D5.S3.Quantum.Fermionic.CoordinateAverage

open Matrix NormedSpace
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
open D5.S3.Quantum.Fermionic.ConferenceMatrices
open D5.S3.Quantum.Fermionic.CompleteCartesianGraph
open D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
open D5.S3.Quantum.Fermionic.CoordinateCliffordSpectrum
open D5.S3.Quantum.Fermionic.CoordinateAverage
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.Fermionic.PhysicalSiteProducts
open D5.S3.Quantum.Fermionic.FlatCliffordGround
open D5.S3.Quantum.Fermionic.GibbsProductGap

noncomputable section
namespace D5.S3.Quantum.Fermionic.GaussianHighDegreeSharpness

open Classical in
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ c : ℝ, c < 1 → ∀ D₀ : ℕ,
    ∃ n D : ℕ, ∃ G : SimpleGraph (Fin n),
    ∃ K : G.edgeSet → Matrix (Fin m × Bool) (Fin m × Bool) ℝ,
    ∃ hH : IsSelfAdjoint (averagedHamiltonian G K),
      1 ≤ n ∧ D₀ ≤ D ∧ 1 ≤ D ∧ G.IsRegularOfDegree D ∧ admissibleEdges G K ∧
      energyGap (averagedHamiltonian G K) = Real.sqrt ((2*m : ℕ) / (D : ℝ)) ∧
      ∃ beta : ℝ, 0 < beta ∧
        freeGap (averagedHamiltonian G K) hH beta > c * Real.sqrt ((2*m : ℕ) / (D : ℝ))

set_option maxHeartbeats 1200000 in
theorem result : claim := by
  classical
  intro m hm c hc D₀
  have hnumbers (m : ℕ) (hm : 1 ≤ m) (D₀ : ℕ) :
    ∃ r n D : ℕ, ∃ e : Fin n ≃ (Fin (2*m) → Index r),
      1 ≤ n ∧ D₀ ≤ D ∧ 1 ≤ D ∧ D = 2*m*(Fintype.card (Index r)-1) ∧
      ((coordinateGraph (2*m) (Index r)).comap e).IsRegularOfDegree D ∧
      ((coordinateGraph (2*m) (Index r)).comap e).edgeFinset.card =
        n*m*(Fintype.card (Index r)-1) := by
    let r := D₀
    let s := Fintype.card (Index r)
    let n := s^(2*m)
    let D := 2*m*(s-1)
    have hs : s = 2^(r+1) := (conference_properties r).1
    have hs2 : 2 ≤ s := by
      rw [hs,pow_succ]
      have hh : 1 ≤ 2^r := Nat.one_le_pow _ _ (by omega)
      omega
    have hsD : D₀ ≤ s-1 := by
      have hh : r+1 < 2^(r+1) := Nat.lt_two_pow_self
      rw [← hs] at hh
      dsimp [r] at hh
      omega
    have hD : 1 ≤ D := Nat.mul_pos (by omega) (by omega)
    have hn : 1 ≤ n := Nat.one_le_pow _ _ (by omega)
    let e : Fin n ≃ (Fin (2*m) → Index r) :=
      Fintype.equivOfCardEq (by simp [n,s])
    let G := (coordinateGraph (2*m) (Index r)).comap e
    have hreg : G.IsRegularOfDegree D := by
      intro v
      have heq : G.degree v = (coordinateGraph (2*m) (Index r)).degree (e v) := by
        rw [← SimpleGraph.card_neighborSet_eq_degree,← SimpleGraph.card_neighborSet_eq_degree]
        let f : G.neighborSet v ≃ (coordinateGraph (2*m) (Index r)).neighborSet (e v) :=
          { toFun := fun w => ⟨e w.val,w.property⟩
            invFun := fun w => ⟨e.symm w.val,by
              change (coordinateGraph (2*m) (Index r)).Adj (e v) (e (e.symm w.val))
              rw [e.apply_symm_apply]
              exact w.property⟩
            left_inv := fun w => by ext; simp
            right_inv := fun w => by ext; simp }
        exact Fintype.card_congr f
      rw [heq]
      exact (regular_and_edge_count (2*m) (Index r)).1 _
    have hedges : G.edgeFinset.card = n*m*(s-1) := by
      have hh := G.sum_degrees_eq_twice_card_edges
      have hr (v : Fin n) : G.degree v = D := hreg v
      simp only [hr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
      dsimp [D] at hh
      nlinarith
    refine ⟨r,n,D,e,hn,?_,hD,rfl,hreg,hedges⟩
    dsimp [D]
    nlinarith
  obtain ⟨r,n,D,e,hn,hD₀,hD,hdegree,hreg,hedges⟩ := hnumbers m hm D₀
  let q := 2*m
  let s := Fintype.card (Index r)
  let a : Fin q ≃ Fin m × Bool := Fintype.equivOfCardEq (by simp [q]; omega)
  let G := (coordinateGraph q (Index r)).comap e
  let K := coordinateCoupling r e a
  let H := averagedHamiltonian G K
  let A := (coordinateSkew q r).submatrix (fun p : Fin n × Fin q => (e p.1,p.2))
    (fun p : Fin n × Fin q => (e p.1,p.2))
  let gamma := fun p : Fin n × Fin q => majorana (finProdFinEquiv (p.1,(a p.2).1)) (a p.2).2
  let Q := (Complex.I/2 : ℂ) • ∑ p, ∑ t, (A p t : ℂ) • (gamma p * gamma t)
  have hs2 : 2 ≤ s := by
    rw [show s = 2^(r+1) from (conference_properties r).1,pow_succ]
    have hh : 1 ≤ 2^r := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hskew : A.transpose = -A := by
    exact congrArg (fun M : Matrix ((Fin q → Index r) × Fin q) ((Fin q → Index r) × Fin q) ℝ =>
      M.submatrix (fun p : Fin n × Fin q => (e p.1,p.2))
        (fun p : Fin n × Fin q => (e p.1,p.2))) (coordinate_skew_flat q r).1
  have hsquare : A*A = (-((s:ℝ)-1)) • 1 := by
    let f := e.prodCongr (Equiv.refl (Fin q))
    change (coordinateSkew q r).submatrix f f * (coordinateSkew q r).submatrix f f = _
    rw [Matrix.submatrix_mul_equiv,(coordinate_skew_flat q r).2]
    change (-((s:ℝ)-1)) • ((1 : Matrix _ _ ℝ).submatrix f f) = _
    rw [Matrix.submatrix_one_equiv]
  have hlabels (p t : Fin n × Fin q) :
      (finProdFinEquiv (p.1,(a p.2).1),(a p.2).2) =
        (finProdFinEquiv (t.1,(a t.2).1),(a t.2).2) ↔ p=t := by
    constructor
    · intro h
      have hfst := finProdFinEquiv.injective (congrArg Prod.fst h)
      have hv : p.1 = t.1 := congrArg (fun x : Fin n × Fin m => x.1) hfst
      have hj : (a p.2).1 = (a t.2).1 := congrArg (fun x : Fin n × Fin m => x.2) hfst
      have hb : (a p.2).2 = (a t.2).2 :=
        congrArg (fun x : Fin (n*m) × Bool => x.2) h
      exact Prod.ext hv (a.injective (Prod.ext hj hb))
    · rintro rfl; rfl
  have hcar := majorana_clifford_and_parity (n*m)
  have hγ (p : Fin n × Fin q) : (gamma p).IsHermitian := hcar.2.2.1 (finProdFinEquiv (p.1,(a p.2).1),(a p.2).2)
  have hCAR (p t : Fin n × Fin q) : gamma p * gamma t + gamma t * gamma p =
      if p=t then (2:ℂ) • 1 else 0 := by
    have hh := hcar.2.2.2.1 (finProdFinEquiv (p.1,(a p.2).1),(a p.2).2)
      (finProdFinEquiv (t.1,(a t.2).1),(a t.2).2)
    simpa only [hlabels] using hh
  have hpar (p : Fin n × Fin q) : numberParity (n*m) * gamma p =
      -(gamma p * numberParity (n*m)) :=
    eq_neg_of_add_eq_zero_left (hcar.2.2.2.2 (finProdFinEquiv (p.1,(a p.2).1),(a p.2).2))
  have hdim : Fintype.card (Assignment (n*m)) = 2^(n*m) := by simp [Assignment]
  have hα : Fintype.card (Fin n × Fin q) = 2*(n*m) := by
    simp only [Fintype.card_prod,Fintype.card_fin,q]
    ring
  have hd : 0 < (s:ℝ)-1 := by
    have hh : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
    linarith
  obtain ⟨hQ,ground,hproj,hphys,heig,hlower⟩ := flat_clifford_ground (n*m) hα hdim
    A hskew ((s:ℝ)-1) hd.le hsquare gamma hγ hCAR (numberParity (n*m)) hpar
  have hAvg : CStarMatrix.ofMatrix.symm H = (G.edgeFinset.card : ℝ)⁻¹ • Q :=
    coordinate_average r e a
  have hform : H = (G.edgeFinset.card : ℝ)⁻¹ • CStarMatrix.ofMatrix Q := by
    exact congrArg CStarMatrix.ofMatrix hAvg
  have hH : IsSelfAdjoint H := by
    rw [hform]
    exact (IsSelfAdjoint.all (G.edgeFinset.card : ℝ)⁻¹).smul hQ
  have had : admissibleEdges G K := (coordinate_edges_admissible r e a).1
  let g := Real.sqrt ((2*m : ℕ)/(D:ℝ))
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos (by exact_mod_cast (show 0<2*m by omega))
    (by exact_mod_cast (show 0<D by omega)))
  change D = 2*m*(s-1) at hdegree
  change G.edgeFinset.card = n*m*(s-1) at hedges
  have hE : (G.edgeFinset.card : ℝ)⁻¹ * (-((n*m:ℕ):ℝ)*Real.sqrt ((s:ℝ)-1)) = -g := by
    have hdlocal : 0 < (s:ℝ)-1 := by
      have hh : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
      linarith
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hsR : 1 ≤ s := by omega
    have hratio : ((2*m:ℕ):ℝ)/(D:ℝ) = 1/((s:ℝ)-1) := by
      rw [hdegree]
      simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hsR,Nat.cast_one]
      field_simp
    dsimp only [g]
    rw [hratio,Real.sqrt_div (by norm_num),Real.sqrt_one]
    rw [hedges]
    simp only [Nat.cast_mul,Nat.cast_sub hsR,Nat.cast_one]
    calc
      _ = -(Real.sqrt ((s:ℝ)-1)/((s:ℝ)-1)) := by field_simp <;> ring
      _ = _ := by rw [Real.sqrt_div_self']
  have heigH : CStarMatrix.ofMatrix.symm H * CStarMatrix.ofMatrix.symm ground.val =
      ((-g : ℝ) : ℂ) • CStarMatrix.ofMatrix.symm ground.val := by
    rw [hAvg,Matrix.smul_mul,heig]
    have hh := congrArg Complex.ofReal hE
    push_cast at hh
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
    push_cast
    rw [← mul_assoc,hh]

  have hground : meanEnergy H ground = -g := by
    unfold meanEnergy
    change (Matrix.trace (CStarMatrix.ofMatrix.symm H * CStarMatrix.ofMatrix.symm ground.val)).re = _
    have ht : Matrix.trace (CStarMatrix.ofMatrix.symm ground.val) = 1 := ground.property.2
    rw [heigH,Matrix.trace_smul,ht]
    simp
  have hlow (rho : DensityState (Assignment (n*m))) : -g ≤ meanEnergy H rho := by
    have hh := mul_le_mul_of_nonneg_left (hlower rho)
      (inv_nonneg.mpr (Nat.cast_nonneg G.edgeFinset.card))
    rw [hE] at hh
    have hmE : meanEnergy H rho = (G.edgeFinset.card : ℝ)⁻¹ *
        meanEnergy (CStarMatrix.ofMatrix Q) rho := by
      unfold meanEnergy
      change (Matrix.trace (CStarMatrix.ofMatrix.symm H * CStarMatrix.ofMatrix.symm rho.val)).re = _
      rw [hAvg,Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re]
      rfl
    rw [hmE]
    exact hh
  have hinf : sInf {x : ℝ | ∃ rho : DensityState (Assignment (n*m)),
      physicalState rho ∧ x = meanEnergy H rho} = -g := by
    apply IsLeast.csInf_eq
    refine ⟨⟨ground,hphys,hground.symm⟩,?_⟩
    rintro x ⟨rho,hp,rfl⟩
    exact hlow rho
  have hprodInf : sInf {x : ℝ | ∃ rho : DensityState (Assignment (n*m)),
      physicalProduct rho ∧ x = meanEnergy H rho} = 0 := by
    let localState := gibbsState (0 : CStarMatrix (Assignment m) (Assignment m) ℂ) (IsSelfAdjoint.zero _)
    have hp : Commute localState.val (CStarMatrix.ofMatrix (numberParity m)) := by
      change Commute ((partitionFunction (0 : CStarMatrix _ _ ℂ))⁻¹ • exp (0 : CStarMatrix _ _ ℂ)) _
      rw [NormedSpace.exp_zero]
      exact (Commute.one_left _).smul_left _
    have hp' : physicalProduct (siteProduct n m (fun _ => localState)) := ⟨_,fun _ => hp,rfl⟩
    apply IsLeast.csInf_eq
    refine ⟨⟨siteProduct n m (fun _ => localState),hp',?_⟩,?_⟩
    · exact (physical_products_zero G K _ hp').symm
    · rintro x ⟨rho,hp,rfl⟩
      rw [physical_products_zero G K rho hp]
  have hgap : energyGap H = g := by unfold energyGap; rw [hprodInf,hinf]; ring
  let B := Real.log (Fintype.card (Assignment (n*m)))
  have hB : 0 ≤ B := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  let beta := (B+1)/((1-c)*g)
  have hbden : 0 < (1-c)*g := mul_pos (sub_pos.mpr hc) hg
  have hbeta : 0 < beta := div_pos (by linarith) hbden
  have hstrict : c*g < g-B/beta := by
    have hx : beta*((1-c)*g)=B+1 := div_mul_cancel₀ _ hbden.ne'
    have hh : B/beta < (1-c)*g := (div_lt_iff₀ hbeta).mpr (by nlinarith [hx])
    nlinarith
  have hfree := (gibbs_product_free_bound G K had hH ground hproj (-g) heigH beta hbeta).2
  refine ⟨n,D,G,K,hH,hn,hD₀,hD,hreg,had,hgap,beta,hbeta,?_⟩
  change c*g < freeGap H hH beta
  exact hstrict.trans_le (by simpa only [neg_neg] using hfree)

end D5.S3.Quantum.Fermionic.GaussianHighDegreeSharpness
