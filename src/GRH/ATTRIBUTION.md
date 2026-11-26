# Attribution

Each declaration below adapts or closely follows, in whole or in part and with changes, a definition, statement or proof from Mathlib (Apache License, Version 2.0). Names may omit a namespace. Mathlib names and files are those of commit 56a005855ea17e0b0958f73ec801ae140b0a1679 (the names also occur, in the same files, at 0df444a360eaa60ab8c11dca51a86af692955474).

| file | declaration | Mathlib declaration | Mathlib file |
|---|---|---|---|
| `src/Lib/Adelic/Adeles/AdditiveCharBasic.lean` | `one_le_prod_norm_Φ` | `NumberField.InfinitePlace.one_le_of_lt_one` | `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` |
| `src/Lib/Adelic/Adeles/CoprimeValuation.lean` | `DenseRange.eq` | `DenseRange.equalizer` | `Mathlib/Topology/DenseEmbedding.lean` |
| `src/Lib/Adelic/QuotientMeasure/Packing.lean` | `encard_le_of_separated` | `Besicovitch.card_le_of_separated` | `Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean` |
| `src/Lib/Adelic/QuotientMeasure/Unimodular.lean` | `exists_eq_smul_haar` | `MeasureTheory.measure_eq_div_smul` | `Mathlib/MeasureTheory/Group/Prod.lean` |
| `src/Lib/Adelic/Witt/SpaceOperations.lean` | `exists_orthonormal_mul` | `LDL.lowerInv`, `IsWellFounded.wellOrderExtension` | `Mathlib/Analysis/Matrix/LDL.lean`, `Mathlib/Order/Extension/Well.lean` |
| `src/Lib/Analytic/Landau/PolarLandau.lean` | `tendsto_sub_mul_logDeriv_entireL` | `AnalyticAt.tendsto_mul_logDeriv_simple_zero` | `Mathlib/Analysis/Calculus/LogDeriv.lean` |
| `src/Lib/CM/Sigma/CurveTheta.lean` | `exists_lattice_of_g₂_g₃` | `CuspForm.discriminantEquiv` | `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` |
| `src/Lib/CM/Sigma/PadicSeriesDefs.lean` | `taylorAtZero_mul` | `UpperHalfPlane.qExpansion_mul` | `Mathlib/NumberTheory/ModularForms/QExpansion.lean` |
| `src/Lib/ClassField/Global/AlbertBrauerHasseNoether.lean` | `FinPlace.ncard_above_mul_ef_eq_finrank` | `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` | `Mathlib/NumberTheory/RamificationInertia/Galois.lean` |
| `src/Lib/ClassField/Global/AlbertBrauerHasseNoether.lean` | `albert_brauer_hasse_noether` | `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` | `Mathlib/Topology/Algebra/ClopenNhdofOne.lean` |
| `src/Lib/ClassField/Global/ArtinReciprocity.lean` | `artin_reciprocity` | `Nat.exists_prime_gt_modEq_one` | `Mathlib/NumberTheory/PrimesCongruentOne.lean` |
| `src/Lib/ClassField/HeckeL/EulerProduct.lean` | `sum_inv_minFac_sq_le_finrank` | `Ideal.card_primesOverFinset_le_finrank` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean` |
| `src/Lib/ClassField/Places/PadicDecomposition.lean` | `norm_zeta_sub_one_pow` | `IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean` |
| `src/Lib/ClassField/Places/ProfiniteGalois.lean` | `finiteDimensional_fixedFieldOf` | `IsGaloisGroup.finiteDimensional` | `Mathlib/FieldTheory/Galois/IsGaloisGroup.lean` |
| `src/Lib/Cohomology/Etale/Functoriality.lean` | `H.dimension_shift_induction` | `CategoryTheory.hasExt_of_enoughInjectives` | `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean` |
| `src/Lib/Cohomology/Etale/Partitions.lean` | `mayer_vietoris_shortExact` | `CategoryTheory.CommSq.shortComplex` | `Mathlib/Algebra/Homology/CommSq.lean` |
| `src/Lib/Cohomology/Hodge/HodgeSite.lean` | `exteriorMap_iotaMulti` | `ExteriorAlgebra.map_apply_ιMulti` | `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` |
| `src/Lib/Cohomology/Hodge/WitnessCocycles.lean` | `homReprEquiv` | `CategoryTheory.uliftCoyonedaEquiv` | `Mathlib/CategoryTheory/Yoneda.lean` |
| `src/Lib/Cohomology/PointClass/HomogeneousCoords.lean` | `CutsOutLocus.isIntegralElem_of_valuationSubring` | `iInf_valuationSubring_superset` | `Mathlib/RingTheory/Valuation/LocalSubring.lean` |
| `src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean` | `aicSubrings.exists_split_mayer_vietoris` | `Ideal.image_subset_nonunits_valuationSubring` | `Mathlib/RingTheory/Valuation/LocalSubring.lean` |
| `src/Lib/Cyclotomic/OddSha/OddShaBound.lean` | `exists_detecting_points_cocycles` | `Ideal.card_primesOverFinset_le_finrank` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean` |
| `src/Lib/Cyclotomic/Voronoi/StickelbergerInteger.lean` | `exists_isStickelbergerBound` | `Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` |
| `src/Lib/DiscreteSeries/Bruhat/BigCell.lean` | `IsL2Contraction.pi` | `MeasureTheory.integral_fintype_prod_eq_prod`, `MeasureTheory.integral_fin_nat_prod_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` |
| `src/Lib/DiscreteSeries/Bruhat/BigCell.lean` | `lintegral_pi_prod` | `MeasureTheory.integral_fintype_prod_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` |
| `src/Lib/DiscreteSeries/Bruhat/ComplexPlace.lean` | `measurePreserving_normSq_sphereDensity` | `MeasureTheory.Measure.volumeIoiPow_apply_Iio` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` |
| `src/Lib/DiscreteSeries/Haar/LogDerivative.lean` | `Haar.det_eq_mul_of_block_triangular` | `LinearMap.det_prodMap` | `Mathlib/LinearAlgebra/Determinant.lean` |
| `src/Lib/DiscreteSeries/Haar/RegularRepL2.lean` | `IsProperMap.monoidHom_id` | `isProperMap_id` | `Mathlib/Topology/Maps/Proper/Basic.lean` |
| `src/Lib/GaloisRep/BaseChange/BaseChangePlaces.lean` | `isCMField_of_forall_exists_conj` | `NumberField.IsCMField.of_forall_isConj` | `Mathlib/NumberTheory/NumberField/CMField.lean` |
| `src/Lib/GaloisRep/Division/MultiplicityFreeSum.lean` | `FreeInts.inv_scalar_on_blocks` | `Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean` |
| `src/Lib/GaloisRep/Main/AttachedDeterminant.lean` | `isStep_stepField` | `pow_sub_one_dvd_differentIdeal_aux`, `dvd_differentIdeal_of_not_isSeparable` | `Mathlib/RingTheory/DedekindDomain/Different.lean` |
| `src/Lib/GaloisRep/Pseudocharacter/SemisimpleReps.lean` | `blockDiagonalAlgHom` | `Matrix.blockDiagonal'RingHom` | `Mathlib/Data/Matrix/Block.lean` |
| `src/Lib/GaloisRep/Pseudocharacter/SemisimpleReps.lean` | `trace_of_idempotent` | `LinearMap.IsIdempotentElem.trace_eq_zero_iff` | `Mathlib/LinearAlgebra/Trace.lean` |
| `src/Lib/General/Algebra/AdicRingHomExt.lean` | `norm_p_lt_one` | `Padic.norm_p_lt_one` | `Mathlib/NumberTheory/Padics/PadicNumbers.lean` |
| `src/Lib/General/Algebra/DisjointUnions.lean` | `H.sigma_bijective` | `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, `CategoryTheory.hasExt_of_enoughInjectives` | `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean`, `Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean` |
| `src/Lib/General/Algebra/FittingDuality.lean` | `exists_matrix_addVal_det_le_length` | `Submodule.finiteQuotient_iff` | `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` |
| `src/Lib/General/Algebra/JetChainRule.lean` | `pderiv_subst` | `PowerSeries.derivative_subst` | `Mathlib/RingTheory/PowerSeries/Derivative.lean` |
| `src/Lib/General/Algebra/MultivariateHensel.lean` | `IsAICLocal.multivariate_hensel` | the `Algebra.Etale` instance | `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` |
| `src/Lib/General/Analysis/FundamentalDomain.lean` | `IsDualFamily.fourier_inversion` | `UnitAddTorus.hasSum_mFourier_series_of_summable`, `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` | `Mathlib/Analysis/Fourier/AddCircleMulti.lean` |
| `src/Lib/General/Analysis/HolomorphicIntegral.lean` | `eventually_differentiableAt_integral` | `continuousWithinAt_clm_apply` | `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` |
| `src/Lib/General/Analysis/OstrowskiTaussky.lean` | `rootCoeffEval_map` | `WittVector.IsPoly.map` | `Mathlib/RingTheory/WittVector/IsPoly.lean` |
| `src/Lib/General/Analysis/ZpowSum.lean` | `nullstellensatz_exists_le_ker` | `finite_of_algHom_finiteType_of_isJacobsonRing`, `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` | `Mathlib/RingTheory/Jacobson/Ring.lean`, `Mathlib/RingTheory/Nullstellensatz.lean` |
| `src/Lib/General/Geometry/ConstantFunctions.lean` | `le_ker_iff_factors` | `AlgebraicGeometry.eq_bot_of_comp_quotientMk_eq_sigmaSpec` | `Mathlib/AlgebraicGeometry/PointsPi.lean` |
| `src/Lib/General/Geometry/LocalTerms.lean` | `restrictAlg` | `Algebra.restrictScalars`, `Algebra.compHom` | `Mathlib/Algebra/Algebra/RestrictScalars.lean`, `Mathlib/Algebra/Algebra/Defs.lean` |
| `src/Lib/General/Geometry/ProperSchemes.lean` | `exists_finiteType_atlas` | `AlgebraicGeometry.compactSpace_iff_exists` | `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean` |
| `src/Lib/General/Geometry/SeparatingPoints.lean` | `IsSeparatingFamily.hom_ext` | `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, `AlgebraicGeometry.ext_of_isDominant_of_isSeparated` | `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` |
| `src/Lib/General/Groups/IndexOfProduct.lean` | `index_pi_univ` | `Subgroup.index_pi` | `Mathlib/GroupTheory/Index.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `adjugate_fin_succ_eq_det_submatrix'` | `Matrix.adjugate_fin_succ_eq_det_submatrix` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `charpoly_fromBlocks_zero₂₁'` | `Matrix.charpoly_fromBlocks_zero₂₁` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_fromBlocks_one₁₁'` | `Matrix.det_fromBlocks_one₁₁` | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_fromBlocks_one₂₂'` | `Matrix.det_fromBlocks_one₂₂` | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_fromBlocks_zero₁₂'` | `Matrix.det_fromBlocks_zero₁₂` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_fromBlocks_zero₂₁'` | `Matrix.det_fromBlocks_zero₂₁` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_kronecker'` | `Matrix.det_kronecker` | `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_succ_column'` | `Matrix.det_succ_column` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_succ_column_zero'` | `Matrix.det_succ_column_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_succ_row'` | `Matrix.det_succ_row` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_succ_row_zero'` | `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `det_vandermonde_ne_zero_iff'` | `Matrix.det_vandermonde_ne_zero_iff` | `Mathlib/LinearAlgebra/Vandermonde.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `fromBlocks_one'` | `Matrix.fromBlocks_one` | `Mathlib/Data/Matrix/Block.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `inv_fromBlocks_zero₂₁_of_isUnit_iff'` | `Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff` | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `isUnit_fromBlocks_zero₁₂'` | `Matrix.isUnit_fromBlocks_zero₁₂` | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `isUnit_fromBlocks_zero₂₁'` | `Matrix.isUnit_fromBlocks_zero₂₁` | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` |
| `src/Lib/General/LinearAlgebra/Base.lean` | `twoBlockTriangular_det₀` | `Matrix.twoBlockTriangular_det` | `Mathlib/LinearAlgebra/Matrix/Block.lean` |
| `src/Lib/General/LinearAlgebra/BlockDiagonalDet.lean` | `sq_le_norm_det_blockDiagPart` | `Matrix.IsHermitian.det_abs` | `Mathlib/Analysis/Matrix/Order.lean` |
| `src/Lib/General/LinearAlgebra/CommonEigenvectors.lean` | `exists_ringEquiv_extend` | `IsAlgClosed.ringEquiv_of_equiv_of_charZero` | `Mathlib/FieldTheory/IsAlgClosed/Classification.lean` |
| `src/Lib/General/LinearAlgebra/HaarUnique.lean` | `measurePreserving_sigma` | `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` | `Mathlib/MeasureTheory/Constructions/Pi.lean` |
| `src/Lib/General/LinearAlgebra/PartialDerivComm.lean` | `levelSpace` | `Representation.invariants` | `Mathlib/RepresentationTheory/Invariants.lean` |
| `src/Lib/General/LinearAlgebra/SmoothMatrices.lean` | `exists_contDiff_eventuallyEq` | `SmoothBumpFunction.contMDiff_smul`, `SmoothPartitionOfUnity.contMDiff_smul` | `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`, `Mathlib/Geometry/Manifold/BumpFunction.lean` |
| `src/Lib/General/Measure/Place.lean` | `continuous_lintegral_and_lt_top` | `continuousOn_integral_of_compact_support` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `src/Lib/General/NumberTheory/QuadField.lean` | `totient_mul_totient_le_finrank` | `IsPrimitiveRoot.lcm_totient_le_finrank` | `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` |
| `src/Lib/General/NumberTheory/ZeroSymmetry.lean` | `prod_euler_factor_ne_zero` | `DirichletCharacter.LFunction_changeLevel` | `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` |
| `src/Lib/LocalGL/Green/MackeyFormula.lean` | `Hall.charpoly_endOnSub_mul_endOnQuot` | `LinearMap.det_eq_det_mul_det` | `Mathlib/LinearAlgebra/Determinant.lean` |
| `src/Lib/PadicComparison/Crystalline/CrystallineEtale.lean` | `exists_etale_lift` | `Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg`, the `Algebra.Etale` instance | `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` |
| `src/Lib/PadicComparison/Descent/ReductionModP.lean` | `isSMulRegular_tensor_of_flat_mod` | `IsSMulRegular.lTensor` | `Mathlib/RingTheory/Regular/IsSMulRegular.lean` |
| `src/Lib/PadicComparison/HodgeTate/GenericFibreTests.lean` | `PadicTest.thetaGeneric` | `fontaineThetaInvertP` | `Mathlib/RingTheory/Perfectoid/BDeRham.lean` |
| `src/Lib/PadicHodge/PeriodRings/AmaxStructure.lean` | `BdRPlus` | `BDeRhamPlus` | `Mathlib/RingTheory/Perfectoid/BDeRham.lean` |
| `src/Lib/PadicHodge/PeriodRings/CpIntegers.lean` | `intQpBar` | `PadicComplexInt` | `Mathlib/NumberTheory/Padics/Complex.lean` |
| `src/Lib/PadicHodge/PeriodRings/CpIntegers.lean` | `witt_hom_ext` | `WittVector.eq_of_apply_teichmuller_eq` | `Mathlib/RingTheory/WittVector/TeichmullerSeries.lean` |
| `src/Lib/PadicHodge/PeriodRings/CpIntegers.lean` | instance `IsDomain (PreTilt R p)` | `PreTilt.isDomain` | `Mathlib/RingTheory/Perfection.lean` |
| `src/Lib/PadicHodge/WachGamma/Letters.lean` | `ainfLattice_eq_span_basis` | `Module.Basis.ofZLatticeBasis` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` |
| `src/Lib/Shimura/AbelianScheme/KernelRing.lean` | `AddObj` | `CategoryTheory.CommGrpObj` | `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` |
| `src/Lib/Shimura/AbelianScheme/KernelRing.lean` | `pullbackAddObj` | `CategoryTheory.Functor.isCommMonObj_obj` | `Mathlib/CategoryTheory/Monoidal/CommMon_.lean` |
| `src/Lib/Shimura/AbelianScheme/Specialisation.lean` | `stalkMap_injective_of_flat` | `AlgebraicGeometry.Flat.epi_of_flat_of_surjective` | `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` |
| `src/Lib/Shimura/AbelianScheme/ThetaFamily.lean` | `finite_flat_of_quasiFinite` | `isDedekindDomainDvr.of_formallyUnramified` | `Mathlib/RingTheory/Unramified/Dedekind.lean` |
| `src/Lib/Shimura/AbelianScheme/ThetaFamily.lean` | `relIndex_comap_lattice` | `ZLattice.covolume_div_covolume_eq_relIndex` | `Mathlib/Algebra/Module/ZLattice/Covolume.lean` |
| `src/Lib/Shimura/Eigenspace/EigenQuotient.lean` | `exists_isEigenQuotient` | `PiTensorProduct.submodule_span_eq_top` | `Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean` |
| `src/Lib/Shimura/HeckeTower/WildType.lean` | `entryConj` | `MonoidHom.restrict` | `Mathlib/Algebra/Group/Submonoid/Operations.lean` |
| `src/Lib/Shimura/ThetaModuli/FamilyFromPoints.lean` | `exists_isAbelianScheme` | `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` | `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` |
| `src/Lib/Shimura/ThetaNormality/NormalGeneration.lean` | `exists_arc` | `Ideal.map_height_le_one_of_mem_minimalPrimes`, `AlgebraicGeometry.ValuativeCriterion.Existence.specializingMap` | `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` |
| `src/Lib/Shimura/ThetaNormality/NormalGeneration.lean` | `map_homogeneousSubmodule_eq_formSpan` | `Ideal.span_pow_eq_map_homogeneousSubmodule`, `Ideal.span_eq_map_homogeneousSubmodule` | `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` |
| `src/Lib/Shimura/Uniformisation/LieExponential.lean` | `coe_fourierChar_eq_exp` | `Real.fourierChar_apply` | `Mathlib/Analysis/Complex/Circle.lean` |
| `src/Lib/Shimura/Uniformisation/ThetaCoords.lean` | `card_torsionBySet_adelicTorsion` | `NumberField.absNorm_differentIdeal` | `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` |
| `src/Lib/Weil/DualPair/Kronecker.lean` | `kroneckerGL` | `Matrix.GeneralLinearGroup.kronecker` | `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` |
| `src/Lib/Weil/Unramified/HeckeGL.lean` | `eventually_localCongruence_subset` | `Valued.tendsto_zero_pow_of_v_lt_one` | `Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` |
| `src/New/Lift/ExponentTheorems.lean` | `KummerChart.few_low_jumps` | `Ideal.sum_ramification_inertia_eq_finrank_fiber` | `Mathlib/RingTheory/RamificationInertia/Basic.lean` |
| `src/New/Selmer/Corepresentable.lean` | `pointChar` | `AddChar.zmodChar` | `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean` |
| `src/New/Selmer/RibetCramer.lean` | `blockFlattenAlgEquiv` | `Matrix.compAlgEquiv` | `Mathlib/Data/Matrix/Composition.lean` |

## Copyright and author lines of these Mathlib files

| Mathlib file | copyright | authors |
|---|---|---|
| `Mathlib/Algebra/Algebra/Defs.lean` | Copyright (c) 2018 Kenny Lau. All rights reserved. | Authors: Kenny Lau, Yury Kudryashov |
| `Mathlib/Algebra/Algebra/RestrictScalars.lean` | Copyright (c) 2018 Kenny Lau. All rights reserved. | Authors: Kenny Lau, Yury Kudryashov |
| `Mathlib/Algebra/Group/Submonoid/Operations.lean` | Copyright (c) 2018 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard, Amelia Livingston, Yury Kudryashov |
| `Mathlib/Algebra/Homology/CommSq.lean` | Copyright (c) 2024 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean` | Copyright (c) 2025 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean` | Copyright (c) 2025 Nailin Guan. All rights reserved. | Authors: Nailin Guan |
| `Mathlib/Algebra/Module/ZLattice/Basic.lean` | Copyright (c) 2023 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/Algebra/Module/ZLattice/Covolume.lean` | Copyright (c) 2024 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten, Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean` | Copyright (c) 2022 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten, Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` | Copyright (c) 2026 Christian Merten. All rights reserved. | Authors: Christian Merten |
| `Mathlib/AlgebraicGeometry/PointsPi.lean` | Copyright (c) 2024 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` | Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved. | Authors: Andrew Yang, Qi Ge, Christian Merten |
| `Mathlib/Analysis/Calculus/LogDeriv.lean` | Copyright (c) 2024 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/Analysis/Complex/Circle.lean` | Copyright (c) 2021 Heather Macbeth. All rights reserved. | Authors: Heather Macbeth |
| `Mathlib/Analysis/Fourier/AddCircleMulti.lean` | Copyright (c) 2023 David Loeffler. All rights reserved. | Authors: David Loeffler |
| `Mathlib/Analysis/Matrix/LDL.lean` | Copyright (c) 2022 Alexander Bentkamp. All rights reserved. | Authors: Alexander Bentkamp |
| `Mathlib/Analysis/Matrix/Order.lean` | Copyright (c) 2025 Monica Omar. All rights reserved. | Authors: Monica Omar |
| `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` | Copyright (c) 2019 Sébastien Gouëzel. All rights reserved. | Authors: Sébastien Gouëzel |
| `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` | Copyright (c) 2025 Yaël Dillies. All rights reserved. | Authors: Yaël Dillies |
| `Mathlib/CategoryTheory/Monoidal/CommMon_.lean` | Copyright (c) 2020 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/CategoryTheory/Yoneda.lean` | Copyright (c) 2017 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/Data/Matrix/Block.lean` | Copyright (c) 2018 Ellen Arlt. All rights reserved. | Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin |
| `Mathlib/Data/Matrix/Composition.lean` | Copyright (c) 2024 Yunzhou Xie. All rights reserved. | Authors: Kevin Buzzard, Yunzhou Xie, Eric Wieser |
| `Mathlib/FieldTheory/Galois/IsGaloisGroup.lean` | Copyright (c) 2025 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/FieldTheory/IsAlgClosed/Classification.lean` | Copyright (c) 2022 Chris Hughes. All rights reserved. | Authors: Chris Hughes |
| `Mathlib/Geometry/Manifold/BumpFunction.lean` | Copyright (c) 2021 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` | Copyright (c) 2021 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/GroupTheory/Index.lean` | Copyright (c) 2021 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/LinearAlgebra/Determinant.lean` | Copyright (c) 2019 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen |
| `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` | Copyright (c) 2020 Adam Topaz. All rights reserved. | Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser |
| `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` | Copyright (c) 2025 Xavier Roblot. All rights reserved. | Authors: Anne Baanen, Xavier Roblot |
| `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` | Copyright (c) 2019 Anne Baanen. All rights reserved. | Authors: Anne Baanen |
| `Mathlib/LinearAlgebra/Matrix/Block.lean` | Copyright (c) 2019 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Wen Yang |
| `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | Copyright (c) 2020 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean` | Copyright (c) 2024 Johan Commelin. All rights reserved. | Authors: Johan Commelin |
| `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | Copyright (c) 2018 Kenny Lau. All rights reserved. | Authors: Kenny Lau, Chris Hughes, Anne Baanen |
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` | Copyright (c) 2021 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` | Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved. | Authors: Filippo A. E. Nuccio, Eric Wieser |
| `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` | Copyright (c) 2022 Alexander Bentkamp. All rights reserved. | Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin |
| `Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean` | Copyright (c) 2026 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/LinearAlgebra/Trace.lean` | Copyright (c) 2019 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle |
| `Mathlib/LinearAlgebra/Vandermonde.lean` | Copyright (c) 2020 Anne Baanen. All rights reserved. | Authors: Anne Baanen, Peter Nelson |
| `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` | Copyright (c) 2023 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/MeasureTheory/Constructions/Pi.lean` | Copyright (c) 2020 Floris van Doorn. All rights reserved. | Authors: Floris van Doorn |
| `Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean` | Copyright (c) 2021 Sébastien Gouëzel. All rights reserved. | Authors: Sébastien Gouëzel |
| `Mathlib/MeasureTheory/Group/Prod.lean` | Copyright (c) 2021 Floris van Doorn. All rights reserved. | Authors: Floris van Doorn |
| `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` | Copyright (c) 2020 Zhouhang Zhou. All rights reserved. | Authors: Zhouhang Zhou, Yury Kudryashov |
| `Mathlib/MeasureTheory/Integral/Pi.lean` | Copyright (c) 2023 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` | Copyright (c) 2022 Riccardo Brasca. All rights reserved. | Authors: Alex J. Best, Riccardo Brasca, Eric Rodriguez |
| `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` | Copyright (c) 2024 David Loeffler. All rights reserved. | Authors: David Loeffler, Michael Stoll |
| `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean` | Copyright (c) 2022 Michael Stoll. All rights reserved. | Authors: Michael Stoll |
| `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` | Copyright (c) 2026 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/NumberTheory/ModularForms/QExpansion.lean` | Copyright (c) 2024 David Loeffler. All rights reserved. | Authors: David Loeffler |
| `Mathlib/NumberTheory/NumberField/CMField.lean` | Copyright (c) 2025 X. Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean` | Copyright (c) 2025 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` | Copyright (c) 2022 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/Padics/Complex.lean` | Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved. | Authors: María Inés de Frutos-Fernández |
| `Mathlib/NumberTheory/Padics/PadicNumbers.lean` | Copyright (c) 2018 Robert Y. Lewis. All rights reserved. | Authors: Robert Y. Lewis |
| `Mathlib/NumberTheory/PrimesCongruentOne.lean` | Copyright (c) 2020 Riccardo Brasca. All rights reserved. | Authors: Riccardo Brasca |
| `Mathlib/NumberTheory/RamificationInertia/Basic.lean` | Copyright (c) 2022 Anne Baanen. All rights reserved. | Authors: Anne Baanen |
| `Mathlib/NumberTheory/RamificationInertia/Galois.lean` | Copyright (c) 2024 Yongle Hu. All rights reserved. | Authors: Yongle Hu, Jiedong Jiang |
| `Mathlib/Order/Extension/Well.lean` | Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved. | Authors: Yaël Dillies, Junyan Xu |
| `Mathlib/RepresentationTheory/Invariants.lean` | Copyright (c) 2022 Antoine Labelle. All rights reserved. | Authors: Antoine Labelle |
| `Mathlib/RingTheory/DedekindDomain/Different.lean` | Copyright (c) 2023 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Wanyi He, Jiedong Jiang, Christian Merten, Jingting Wang, Andrew Yang, Shouxin Zhang |
| `Mathlib/RingTheory/Jacobson/Ring.lean` | Copyright (c) 2020 Devon Tuma. All rights reserved. | Authors: Devon Tuma |
| `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` | Copyright (c) 2020 Johan Commelin. All rights reserved. | Authors: Johan Commelin, Eric Wieser |
| `Mathlib/RingTheory/Nullstellensatz.lean` | Copyright (c) 2021 Devon Tuma. All rights reserved. | Authors: Devon Tuma |
| `Mathlib/RingTheory/Perfection.lean` | Copyright (c) 2020 Kenny Lau. All rights reserved. | Authors: Kenny Lau |
| `Mathlib/RingTheory/Perfectoid/BDeRham.lean` | Copyright (c) 2025 Jiedong Jiang. All rights reserved. | Authors: Jiedong Jiang |
| `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/RingTheory/PowerSeries/Derivative.lean` | Copyright (c) 2023 Richard M. Hill. All rights reserved. | Authors: Richard M. Hill, Ralf Stephan |
| `Mathlib/RingTheory/RamificationInertia/Basic.lean` | Copyright (c) 2026 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/RingTheory/Regular/IsSMulRegular.lean` | Copyright (c) 2024 Brendan Murphy. All rights reserved. | Authors: Brendan Murphy |
| `Mathlib/RingTheory/Smooth/NoetherianDescent.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Judith Ludwig, Christian Merten |
| `Mathlib/RingTheory/Unramified/Dedekind.lean` | Copyright (c) 2026 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/RingTheory/Valuation/LocalSubring.lean` | Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu. All rights reserved. | Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu |
| `Mathlib/RingTheory/WittVector/IsPoly.lean` | Copyright (c) 2020 Johan Commelin. All rights reserved. | Authors: Johan Commelin, Robert Y. Lewis |
| `Mathlib/RingTheory/WittVector/TeichmullerSeries.lean` | Copyright (c) 2025 Jiedong Jiang. All rights reserved. | Authors: Jiedong Jiang |
| `Mathlib/Topology/Algebra/ClopenNhdofOne.lean` | Copyright (c) 2024 Nailin Guan. All rights reserved. | Authors: Nailin Guan, Yi Song, Xuchun Li, Bryan Wang |
| `Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` | Copyright (c) 2025 Salvatore Mercuri. All rights reserved. | Authors: Salvatore Mercuri |
| `Mathlib/Topology/DenseEmbedding.lean` | Copyright (c) 2019 Reid Barton. All rights reserved. | Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot |
| `Mathlib/Topology/Maps/Proper/Basic.lean` | Copyright (c) 2023 Anatole Dedecker. All rights reserved. | Authors: Anatole Dedecker, Etienne Marion |
