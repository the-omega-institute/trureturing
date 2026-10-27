/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The full automorphism maximum for simple complex evolution algebras. -/

/-
result:
  proof_shape: content
  escape_witness: coordinate_simple_bound
  admission_basis: open-problem-resolution (#21769; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22095
The simplicity predicate and maximum statement retain the source expressions.
The coordinate product, pair-product span and full automorphism group use their existing owners.
Content declarations name their live mathematical witness below. Frozen identities use the merged-base report.
Declarations (proof_shape; consumers; direct frozen dependency labels):
  IsSimple: bind-only; consumers: claim, complete_simple, coordinate_simple_bound, cyclic_family, result, simple_bound, simple_of_connected, simple_perfect, simple_support_connected, simple_transport; dependencies: F30
  claim: bind-only; consumers: result; dependencies: F10, F30, F47, F48, F50, F51
  simple_perfect: bind-only; consumers: coordinate_simple_bound; dependencies: F30, F31
  simple_transport: bind-only; consumers: simple_bound; dependencies: F30, F31, F32, F33
  forward_span_ideal: content; escape_witness: forward_span_ideal; consumers: simple_support_connected; dependencies: F21, F24, F47, F48, F49, F55, F56
  simple_support_connected: content; escape_witness: simple_support_connected; consumers: coordinate_simple_bound; dependencies: F21, F24, F30, F47, F48, F49, F55, F56
  simple_of_connected: content; escape_witness: simple_of_connected; consumers: complete_simple, cyclic_family; dependencies: F22, F24, F30, F31, F47, F48, F49, F56
  factorial_binary_base: content; escape_witness: factorial_binary_base; consumers: factorial_period_bound; dependencies: none
  factorial_period_bound: content; escape_witness: factorial_period_bound; consumers: coordinate_simple_bound; dependencies: none
  connected_beta_cycle: content; escape_witness: connected_beta_cycle; consumers: coordinate_simple_bound; dependencies: F3, F5, F6, F7, F9
  equal_fibers: content; escape_witness: equal_fibers; consumers: coordinate_simple_bound; dependencies: F3, F4, F5, F6, F7, F8, F9
  cycle_weight_single: bind-only; consumers: coordinate_simple_bound, cyclic_family; dependencies: F1, F2, F40
  supported_permutation: bind-only; consumers: coordinate_simple_bound; dependencies: F23, F24, F47, F48, F49, F52, F53
  completeLinear: bind-only; consumers: completeProduct, complete_natural, complete_perfect, complete_square, result; dependencies: F47
  completeProduct: bind-only; consumers: completeLift, complete_aut_card, complete_natural, complete_perfect, complete_simple, complete_square, complete_support, result; dependencies: F41, F47, F48
  complete_perfect: bind-only; consumers: complete_aut_card, complete_simple; dependencies: F30, F41, F46, F47, F48, F49, F54
  complete_square: bind-only; consumers: complete_support; dependencies: F41, F42, F43, F44, F45, F47, F48, F49
  complete_support: bind-only; consumers: complete_aut_card, complete_simple; dependencies: F24, F41, F42, F43, F44, F45, F47, F48, F49
  complete_natural: bind-only; consumers: complete_aut_card, complete_simple, result; dependencies: F41, F47, F48, F49
  complete_simple: content; escape_witness: simple_of_connected; consumers: result; dependencies: F22, F24, F30, F31, F41, F42, F43, F44, F45, F46, F47, F48, F49, F54, F56
  completeLift: bind-only; consumers: complete_aut_card; dependencies: F10, F18, F34, F41, F47, F48
  complete_aut_card: content; escape_witness: complete_aut_card; consumers: result; dependencies: F10, F11, F12, F13, F14, F15, F17, F18, F19, F20, F24, F30, F34, F35, F41, F42, F43, F44, F45, F46, F47, F48, F49, F53, F54
  coordinate_simple_bound: content; escape_witness: equal_fibers; consumers: simple_bound; dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F15, F16, F21, F23, F24, F25, F30, F31, F40, F47, F48, F49, F52, F53, F54, F55, F56
  simple_bound: content; escape_witness: coordinate_simple_bound; consumers: result; dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F15, F16, F21, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F40, F47, F48, F49, F52, F53, F54, F55, F56
  cycle_on_finRotate: bind-only; consumers: cyclic_family; dependencies: none
  cyclic_family: content; escape_witness: simple_of_connected; consumers: result; dependencies: F1, F2, F10, F22, F24, F30, F31, F36, F37, F38, F39, F40, F47, F48, F49, F50, F51, F53, F54, F56
  result: content; escape_witness: coordinate_simple_bound; consumers: terminal; dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42, F43, F44, F45, F46, F47, F48, F49, F50, F51, F52, F53, F54, F55, F56
Frozen declaration identities:
  F1: D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.weight
    sha256:f01d9a74dc62ad1748f40d0383cd5b8bc608ff363304170eff81c52661b0c56a
  F2: D5/S3/FiniteGroups/SuccessorPowerAssignments.cycleWeight
    sha256:c7dbd268b831d326c922e7b8556801cb23d0c9a6e79592a27023b23150b387f2
  F3: D5/S3/FiniteGroups/SuccessorQuotient.Blocks
    sha256:3aa675a74132e5ab7ac82115e6e0f885923116eab0d8cfa43567d4f91b174d45
  F4: D5/S3/FiniteGroups/SuccessorQuotient.Fiber
    sha256:a3196f134f31d1100ff3fc78bb3cb2fd814f95e5aa1253e47bd72739905e2d0b
  F5: D5/S3/FiniteGroups/SuccessorQuotient.beta
    sha256:7f3c6a50021f9418a845be9b8f55756bbe5c6feeaa4005a029eb459ef666653a
  F6: D5/S3/FiniteGroups/SuccessorQuotient.least
    sha256:d14a33f1cfbee6c9ca7e0c1bd08d9a65e99b0e78b4e95b677fd5ac95ed53453f
  F7: D5/S3/FiniteGroups/SuccessorQuotient.project
    sha256:e96a370d080e298a6d1330cf403a7ec87026696b24c26798935375626d033c49
  F8: D5/S3/FiniteGroups/SuccessorQuotient.successor
    sha256:680c1ec9dce7b4b5e1ee204536222be776d528574c909fdf59c516c8727d6a85
  F9: D5/S3/FiniteGroups/SuccessorQuotient.successor_project
    sha256:b9eb8ed50a7b1d7e536e56f2b1cd764759f4c1887e58de96af1a6f73e2c6851f
  F10: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.Aut
    sha256:7b6e42bbad7909bfbea2fb10e8af0f720cdef96a57df1be68ebcf3a8a52a0d0e
  F11: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.MonomialData
    sha256:22594f6a9ea421391b668cb13459a37d450fcd906f9d02d7355cb94cdeeba0f3
  F12: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.image
    sha256:904834ecec48ba837eccadf49e383faf74e2486621388521706a77be4aa62aaf
  F13: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.perm
    sha256:7143729637fddcf7a9eb60e94ec5ecf1617136e86ae0657155bd58028a3d9e7c
  F14: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.scalar
    sha256:21d1d70d930c5066383a564d8ac91ed57bea68e2142a6da9ebeaf26228f3e00a
  F15: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_finite
    sha256:cd1dcc152bd49bf48739ecd065eafdfad7c4d48816592e140c741f9b592b1204
  F16: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_quotient_bound
    sha256:10f0e3946d5e36997d4a4f9a2bb904d0dc85879db0be6767897302f3386323ba
  F17: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.monomialData
    sha256:f8b55ba3a2c31a6458df0bace38daa9e5608a0e0c5ad60e334a1a718f2306afc
  F18: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl._proof_1
    sha256:e89332cd1f0ffda12ef795231a6d62e262d6bb4ebe74f39d4d75e7d6b137fae6
  F19: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.rho
    sha256:82899d8212b0ebf759409999fb0ea5ebab42734b87160043a944275b3d7525f6
  F20: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.rho_kernel_iff
    sha256:d789d252777f71c315438bcff2ca06e01aaac24999c1528a6b93d80d56dc029b
  F21: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.squareVector
    sha256:f43e99e15ffef3ef1676b70bcf617651aed5edd3b82674bad151c7d51c50b18f
  F22: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.structureCoefficient
    sha256:64dc65b69db2e245edf0351fdc7dbfc71d4dd9bdcb524ac42e8a2620e0828432
  F23: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.structure_map_injective
    sha256:18fc0f74b149bb95e1cb75ef2d4d6ab23ed26700462462a79257354d9203dbb9
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl.0.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl.structure_map_injective
  F24: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.supportRelation
    sha256:ccdac8435305ec3781873e996633307d447555e6e9d5c0a9d490f12a528f335c
  F25: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.support_positive_degrees
    sha256:0d118dea23829c795a2cd42ae2dfe5d6765c8c43668a3d86115860bf2bbcbe63
  F26: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.automorphismConjugacy
    sha256:5ccad2f498a15410d5406e81a860c552060e0b830f8b0528512d910ef451559d
  F27: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.dimensionBasis
    sha256:62b533628184e52101583e1d5eb53e2faa2acd099af5fefdbaeb88d83cb2e776
  F28: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.dimensionBasis_natural
    sha256:5e0e9caeb43d088d0e550d84ae9813f8a52eb168cd85940cc73655cf8437d437
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport.0.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport.dimensionBasis_natural
  F29: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.natural_basis_transport_iff
    sha256:01ee6b69e3c219d011112d99654cb247c1cf5be9b592e0106c8fe6432d89de59
  F30: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.productSpan
    sha256:41e6b4ecb070fbc51ebb5e12657546e6125de44c39e0f785b91934cc0478d29b
  F31: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport._proof_1
    sha256:4d291e2abbd1e9b486ef8bddd53d22bc7229b4f279386bcd0bd605a97b020d06
  F32: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.product_span_transport
    sha256:0ce54ce87f696aafd54eeefb60204fd67607e4da4dbb197664b0075b5fbb720a
  F33: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.transportProduct
    sha256:2b4f73f0de153f085527863a9e4316ae3249884fdd7cd8f98cb31cb4a19b36ee
  F34: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear
    sha256:d93dfd69544b7343a15a6b70d31b9c0d270e53c5aba909b1f96d5647d4c0c66f
  F35: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear_basis
    sha256:41e9502ed3ed946ac0d120e18719a0589f06953bcb7fc335d6f1a652c70ef744
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.0.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutationLinear_basis
  F36: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationProduct
    sha256:7f37cf1cf44aa15e4b28a892be25165a4fb2c5005d95c66cd4789fed424b4d81
  F37: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_family
    sha256:057fa2fb2304e47baed907ad7f5bc15346ba6cfa7bd423cc0131b4331807ee73
  F38: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_mixed
    sha256:d6c1e860aca9fa1e51cb1303a215fb76a09f509d8bcfa39986d551ff4c913313
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.0.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_mixed
  F39: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_support
    sha256:c25dcb461ed4390ceaf4dd578ab727bbacae74311f06964651bb5f287ecde53e
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.0.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_support
  F40: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.cycle_weight_centralizer
    sha256:370280f3e4c8283d074ba6a7c11b66e6d0e57f36f4c1ac9007ccece6c88b694d
  F41: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinateProduct
    sha256:552ddc3acce8a90e8fe803aa3172e064dd0a3e8280742efe92a43ef178641d06
  F42: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily._proof_1
    sha256:f6addd9d5d28bf471f6c051635f7b3cd71c5885183b1927b51ea197227b8e0ea
  F43: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily._proof_2
    sha256:d8f3c8861e5c4948b13ef16e55e92c6cc329bab9979374fb702d8090af188bff
  F44: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily._proof_5
    sha256:f9194c9f4873768c32cd99a6bd607e6fe23c9071681b3758dfe663fe21f468e6
  F45: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily._proof_8
    sha256:e4ce48c3edeca84170a802067c0c4f175a3cef416571ff508cfe1f57d69b251b
  F46: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinate_product_square
    sha256:1f7af2565c0f691e454d565fa0619c63e23a7b1a4584eaca2473cf66b903645d
  F47: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Coord
    sha256:e13ef22dffbdbfe22335d7405a2f8bddc8c047a0aec25705ccc2a8c92a06486e
  F48: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Product
    sha256:bd172aba00d898917282350fdfc0b2da6bfa27ab78dfc6133713ec6a3ea51585
  F49: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound._proof_1
    sha256:c9fd99d1033cfa1dd99ed092649c0592a65deba8ce9db21c46227052e9fc9838
  F50: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.commutative
    sha256:08d35ae3e13192aeb949c33c7a9cdbbff145e4782c1b6507754b179b75877df5
  F51: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.hasNaturalBasis
    sha256:d82050e618cf37f3eae53e248797f17d42023142fc6bb561ab83007b0e1f0a98
  F52: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.natural_basis_structure_map
    sha256:75bfbf3610f92a50098f0723c05c9edfc3f39e12baee4b6c747347ac2ee92e10
  F53: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.perfect
    sha256:7d4b6b94d5b79062f4395b15c956b4e5a6d6447c409e4d7c48bead6754f9d130
  F54: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.square
    sha256:b1ed58d2a67970e6672454db6fab636e2f87203fe08adee2e1d9b539d4d51612
  F55: D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_left
    sha256:2be8855d2191fa09baceff2fa714b2244c34b9ceb5a3bf56d5805c7d76af56d3
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.0.D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_left
  F56: D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_right
    sha256:0f0601601d3196387a2da4fcb801f6702afdc0d4e6c34dfcb7be9986b06a2b6e
    base declaration: _private.D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.0.D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right
-/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
import D5.S3.FiniteGroups.SuccessorPowerAssignments
import D5.S3.FiniteGroups.SuccessorQuotient
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
import D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
namespace D5.S3.QuadraticForms.EvolutionAlgebras.SimpleEvolutionAutomorphismMaximum
open private D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl.structure_map_injective
  from D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open private D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport.dimensionBasis_natural
  from D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open private D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutationLinear_basis
  D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_mixed
  D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_support
  from D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
open private D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_left
  D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right
  from D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks
open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
open D5.S3.FiniteGroups.SuccessorQuotient
open D5.S3.FiniteGroups.SuccessorPowerAssignments
open D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

/-!
Binding conventions for Kaygorodov--Martín González--Viruel,
arXiv:2610.22248v1, Conjecture 4.

The multiplication is an arbitrary complex bilinear map, without a unit or
associativity assumption. `HuEvolutionLowerBound.Product`, `Coord`,
`commutative`, and `hasNaturalBasis` own the coordinate conventions.
`EvolutionBasisTransport.productSpan` is A², the span of all pair products.
`EvolutionAutomorphismControl.Aut` is the full group of multiplication-preserving
complex linear equivalences, not a subgroup of coordinate permutations.
The existing `structureCoefficient` and `supportRelation` use the source's
row convention: e_i² = sum_j omega_ij e_j, and i -> j iff omega_ij != 0.

The survey leaves the standard definition of simplicity implicit. Its cited
Cabrera Casado--Siles Molina--Velasco source, arXiv:1601.01832v2, Section 4,
says: "We recall that an algebra A is simple if A² != 0 and 0 is the only
proper ideal." Below the ideals are all complex vector subspaces absorbing
products on both sides, not just ideals spanned by a subset of the natural basis.
-/

/-- A² is nonzero and every two-sided complex-linear ideal is zero or all of A. -/
def IsSimple {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : Prop :=
  productSpan μ ≠ ⊥ ∧
    ∀ I : Submodule ℂ A,
      (∀ x : A, x ∈ I → ∀ y : A, μ x y ∈ I ∧ μ y x ∈ I) →
        I = ⊥ ∨ I = ⊤

/-- Conjecture 4: the full group is finite, has the stated upper bound,
and some simple algebra attains that bound in every positive dimension. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ (A : Type*) [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
      (ι : Type*) [Fintype ι],
      ∀ (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A),
        Module.finrank ℂ A = n →
        (∀ i j : ι, i ≠ j → μ (b i) (b j) = 0) →
        (∀ x y : A, μ x y = μ y x) →
        IsSimple μ →
          Finite (Aut μ) ∧
            Nat.card (Aut μ) ≤ max n.factorial (n * (2 ^ n - 1))) ∧
    (∃ μ : Product n,
      Module.finrank ℂ (Coord n) = n ∧
      commutative μ ∧ hasNaturalBasis μ ∧ IsSimple μ ∧
      Finite (Aut μ) ∧
        Nat.card (Aut μ) = max n.factorial (n * (2 ^ n - 1)))

private theorem simple_perfect {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (hs : IsSimple μ) : productSpan μ = ⊤ := by
  exact (hs.2 (productSpan μ) (by
    intro x hx y
    exact ⟨Submodule.subset_span ⟨x,y,rfl⟩,Submodule.subset_span ⟨y,x,rfl⟩⟩)).resolve_left hs.1

private theorem simple_transport {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A ≃ₗ[ℂ] B)
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (hs : IsSimple μ) :
    IsSimple (transportProduct e μ) := by
  constructor
  · intro hz
    apply hs.1
    have he : (productSpan μ).map e.toLinearMap = ⊥ := (product_span_transport e μ).trans hz
    have hle := (Submodule.map_eq_bot_iff).mp he
    simpa using hle
  · intro I hI
    let J := I.comap e.toLinearMap
    have hJ : ∀ x : A, x ∈ J → ∀ y : A, μ x y ∈ J ∧ μ y x ∈ J := by
      intro x hx y
      have hh := hI (e x) hx (e y)
      simpa [J, transportProduct] using hh
    rcases hs.2 J hJ with hj | hj
    · left
      apply le_antisymm _ bot_le
      intro z hz
      have hx : e.symm z ∈ J := by simpa [J] using hz
      rw [hj] at hx
      have hx' : e.symm z = 0 := hx
      simpa using congrArg e hx'
    · right
      apply top_unique
      intro z hz
      have hx : e.symm z ∈ J := by rw [hj]; trivial
      simpa [J] using hx

private theorem forward_span_ideal {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (S : Set (Fin n))
    (hS : ∀ i, i ∈ S → ∀ j, supportRelation μ b i j → j ∈ S) :
    ∀ x, x ∈ Submodule.span ℂ (b '' S) → ∀ y,
      μ x y ∈ Submodule.span ℂ (b '' S) ∧
      μ y x ∈ Submodule.span ℂ (b '' S) := by
  classical
  let I := Submodule.span ℂ (b '' S)
  have hsq (i : Fin n) (hi : i ∈ S) : μ (b i) (b i) ∈ I := by
    apply b.mem_span_image.mpr
    intro j hj
    apply hS i hi j
    exact Finsupp.mem_support_iff.mp hj
  intro x hx y
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    rw [D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_left μ b hb y i,
      D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right μ b hb y i]
    exact ⟨I.smul_mem _ (hsq i hi), I.smul_mem _ (hsq i hi)⟩
  | zero => simp
  | add x z hx hz ihx ihz =>
    simp only [map_add, LinearMap.add_apply]
    exact ⟨I.add_mem ihx.1 ihz.1,I.add_mem ihx.2 ihz.2⟩
  | smul a x hx ih =>
    simp only [map_smul, LinearMap.smul_apply]
    exact ⟨I.smul_mem a ih.1,I.smul_mem a ih.2⟩

private theorem simple_support_connected {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0) (hs : IsSimple μ) :
    ∀ i j, Relation.ReflTransGen (supportRelation μ b) i j := by
  classical
  intro i j
  let S := {k | Relation.ReflTransGen (supportRelation μ b) i k}
  let I := Submodule.span ℂ (b '' S)
  have hI := forward_span_ideal μ b hb S (by
    intro x hx y hxy
    exact hx.tail hxy)
  have hne : I ≠ ⊥ := by
    intro hz
    have hi : b i ∈ I := Submodule.subset_span ⟨i, Relation.ReflTransGen.refl, rfl⟩
    rw [hz] at hi
    exact b.ne_zero i hi
  have ht := (hs.2 I hI).resolve_left hne
  have hj : b j ∈ I := by rw [ht]; trivial
  exact b.self_mem_span_image.mp hj

private theorem simple_of_connected {n : ℕ} (hn : 1 ≤ n) (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hp : productSpan μ = ⊤)
    (hc : ∀ i j, Relation.ReflTransGen (supportRelation μ b) i j) :
    IsSimple μ := by
  classical
  haveI : Nontrivial (Coord n) := by
    haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
    infer_instance
  refine ⟨by rw [hp]; exact top_ne_bot, ?_⟩
  intro I hI
  by_cases hz : I = ⊥
  · exact Or.inl hz
  right
  obtain ⟨x,hx,hx0⟩ := I.ne_bot_iff.mp hz
  have hi : ∃ i, b.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i,hi⟩ := hi
  have hsq : μ (b i) (b i) ∈ I := by
    have hh := (hI x hx (b i)).1
    rw [D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right μ b hb x i] at hh
    exact (I.smul_mem_iff hi).mp hh
  have hall (j : Fin n) : μ (b j) (b j) ∈ I := by
    have h := hc i j
    induction h with
    | refl => exact hsq
    | @tail j k hij hjk ih =>
      have hh := (hI (μ (b j) (b j)) ih (b k)).1
      rw [D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right μ b hb (μ (b j) (b j)) k] at hh
      exact (I.smul_mem_iff hjk).mp hh
  apply top_unique
  rw [← hp]
  apply Submodule.span_le.mpr
  rintro z ⟨x,y,rfl⟩
  rw [← b.sum_repr y, map_sum]
  apply I.sum_mem
  intro j hj
  rw [map_smul, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mul_basis_right μ b hb x j]
  exact I.smul_mem _ (I.smul_mem _ (hall j))

private theorem factorial_binary_base (h : ℕ) (hh : 2 ≤ h) :
    h * (2 ^ h - 1) * 2 ^ h ≤ (2 * h).factorial := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    have hp : 2 ≤ 2 ^ h := by
      exact (by norm_num : 2 ≤ (2:ℕ)^2).trans (Nat.pow_le_pow_right (by omega) hh)
    have hm : 2 ^ (h + 1) - 1 ≤ h * (2 * h + 1) * (2 ^ h - 1) := by
      calc
        _ ≤ 3 * (2 ^ h - 1) := by rw [pow_succ]; omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith)
    calc
      (h+1) * (2 ^ (h+1) - 1) * 2 ^ (h+1) =
          ((h+1)*2*2^h) * (2^(h+1)-1) := by rw [pow_succ]; ring
      _ ≤ ((h+1)*2*2^h) * (h*(2*h+1)*(2^h-1)) := Nat.mul_le_mul_left _ hm
      _ = ((2*h+2)*(2*h+1)) * (h*(2^h-1)*2^h) := by ring
      _ ≤ ((2*h+2)*(2*h+1)) * (2*h).factorial := Nat.mul_le_mul_left _ ih
      _ = (2*(h+1)).factorial := by
        rw [show 2*(h+1) = (2*h+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
        ring

private theorem factorial_period_bound (h k : ℕ) (hh : 2 ≤ h) (hk : 2 ≤ k) :
    h * (2 ^ h - 1) * k.factorial ^ h ≤ (h * k).factorial := by
  induction k, hk using Nat.le_induction with
  | base => simpa [Nat.mul_comm] using factorial_binary_base h hh
  | succ k hk ih =>
    have hm : (k+1)^h ≤ (h*k+1).ascFactorial h :=
      (Nat.pow_le_pow_left (by nlinarith) h).trans (Nat.pow_succ_le_ascFactorial _ _)
    calc
      h*(2^h-1)*((k+1).factorial)^h =
          (h*(2^h-1)*k.factorial^h)*(k+1)^h := by rw [Nat.factorial_succ, mul_pow]; ring
      _ ≤ (h*k).factorial * (h*k+1).ascFactorial h := Nat.mul_le_mul ih hm
      _ = (h*(k+1)).factorial := by
        simpa only [Nat.mul_add,Nat.mul_one] using Nat.factorial_mul_ascFactorial (h*k) h

private theorem connected_beta_cycle {V : Type*} [Finite V] (R : V → V → Prop)
    (ho : ∀ x, ∃ y, R x y) (hi : ∀ y, ∃ x, R x y)
    (hc : ∀ x y, Relation.ReflTransGen R x y) :
    (beta R ho hi).IsCycleOn Set.univ := by
  let β := beta R ho hi
  have hp {x y : V} (h : Relation.ReflTransGen R x y) :
      β.SameCycle (project R x) (project R y) := by
    induction h with
    | refl => exact Equiv.Perm.SameCycle.rfl
    | @tail y z h hyz ih =>
      have hh : β (project R y) = project R z := successor_project R ho hyz
      rw [← hh]
      exact ih.apply_right
  refine ⟨β.bijective.bijOn_univ, ?_⟩
  intro q hq q' hq'
  induction q using Quotient.inductionOn with | h x =>
    induction q' using Quotient.inductionOn with | h y =>
      exact hp (hc x y)

private theorem equal_fibers {n : ℕ} (hn : 1 ≤ n) (R : Fin n → Fin n → Prop)
    (ho : ∀ x, ∃ y, R x y) (hi : ∀ y, ∃ x, R x y)
    (hc : (beta R ho hi).IsCycleOn Set.univ)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ x, R x (σ x)) :
    ∃ k : ℕ, 1 ≤ k ∧ n = Nat.card (Blocks R) * k ∧
      ∀ q : Blocks R, Nat.card (Fiber R q) = k := by
  classical
  letI := Fintype.ofFinite (Blocks R)
  let q₀ := project R (⟨0, by omega⟩ : Fin n)
  let β := beta R ho hi
  let k := Nat.card (Fiber R q₀)
  have hnext (q : Blocks R) : Nat.card (Fiber R (β q)) = Nat.card (Fiber R q) := by
    let e : Fiber R q ≃ Fiber R (β q) := σ.subtypeEquiv (fun x => by
      change project R x = q ↔ project R (σ x) = beta R ho hi q
      rw [← successor_project R ho (hσ x)]
      exact (beta R ho hi).injective.eq_iff.symm)
    exact (Nat.card_congr e).symm
  have hall (q : Blocks R) : Nat.card (Fiber R q) = k := by
    obtain ⟨m,hm⟩ := Equiv.Perm.IsCycleOn.exists_pow_eq' Set.finite_univ hc (Set.mem_univ q₀) (Set.mem_univ q)
    rw [← hm]
    clear hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hnext _).trans ih
  haveI : Nonempty (Fiber R q₀) := ⟨⟨⟨0,by omega⟩,rfl⟩⟩
  refine ⟨k, Nat.card_pos, ?_, hall⟩
  have hsum : ∑ q : Blocks R, Nat.card (Fiber R q) = n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sigmaFiberEquiv (project R))
  simp only [hall,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  simpa only [Nat.card_eq_fintype_card,Nat.cast_id] using hsum.symm

private theorem cycle_weight_single {Q : Type*} [Fintype Q] [Nonempty Q]
    (β : Equiv.Perm Q) (hc : β.IsCycleOn Set.univ) :
    cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm Q))) =
      Fintype.card Q * (2 ^ Fintype.card Q - 1) := by
  classical
  rw [cycle_weight_centralizer]
  have hpart : β.partition.parts = {Fintype.card Q} := by
    by_cases hq : Fintype.card Q ≤ 1
    · haveI : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp hq
      have he : β = 1 := Subsingleton.elim _ _
      have hn : Fintype.card Q = 1 := Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary Q,
        fun _ => Subsingleton.elim _ _⟩
      simp [he, Equiv.Perm.parts_partition, hn]
    · haveI : Nontrivial Q := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hcyc : β.IsCycle := Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
        ⟨Set.univ, Set.nontrivial_univ, hc, by intros; trivial⟩
      have hsupport : β.support = Finset.univ := by
        ext q
        simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
        exact hc.apply_ne Set.nontrivial_univ (Set.mem_univ q)
      simp [Equiv.Perm.parts_partition, hcyc.cycleType, hsupport]
  rw [hpart]
  simp [weight]

private theorem supported_permutation {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, supportRelation μ b i (σ i) := by
  classical
  obtain ⟨M,hM⟩ := natural_basis_structure_map μ b hb
  have hMi := D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl.structure_map_injective μ b hp M hM
  have hdet : (LinearMap.toMatrix' M).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    intro hz
    have hk := (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
    exact hk (LinearMap.ker_eq_bot.mpr hMi)
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ,_,hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  refine ⟨σ,?_⟩
  intro i
  have hentry : LinearMap.toMatrix' M (σ i) i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hσ).2) i (Finset.mem_univ i)
  have he : b.equivFun (μ (b i) (b i)) = M (Pi.single i 1) := by
    have hi : b.equivFun (b i) * b.equivFun (b i) = Pi.single i 1 := by
      simpa only [Module.Basis.equivFun_apply, Module.Basis.repr_self,
        Finsupp.single_eq_pi_single, mul_one] using
        (Pi.single_mul (α := fun _ : Fin n => ℂ) i (1 : ℂ) 1).symm
    simpa only [hi] using hM (b i) (b i)
  change b.equivFun (μ (b i) (b i)) (σ i) ≠ 0
  rw [he]
  exact hentry

private noncomputable def completeLinear (n : ℕ) : Coord n →ₗ[ℂ] Coord n :=
  LinearMap.id + LinearMap.pi (fun _ => ∑ j : Fin n, LinearMap.proj j)

private noncomputable def completeProduct (n : ℕ) : Product n := coordinateProduct (completeLinear n)

private theorem complete_perfect (n : ℕ) : productSpan (completeProduct n) = ⊤ := by
  have hi : Function.Injective (completeLinear n) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    have hx' (i : Fin n) : x i + ∑ j, x j = 0 := by
      simpa [completeLinear, LinearMap.sum_apply] using congrFun hx i
    have hs : (∑ j, x j) + (n : ℂ)*(∑ j, x j) = 0 := by
      have hh := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hx' i)
      simpa [Finset.sum_add_distrib] using hh
    have hn : (1 : ℂ) + n ≠ 0 := by exact_mod_cast (by omega : (1:ℕ)+n ≠ 0)
    have hm : ((1:ℂ)+n)*(∑ j,x j)=0 := by simpa [add_mul] using hs
    have hz : ∑ j, x j = 0 := (mul_eq_zero.mp hm).resolve_left hn
    ext i
    simpa [hz] using hx' i
  have hr : LinearMap.range (completeLinear n) = ⊤ :=
    LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective).mp hi)
  have hh := coordinate_product_square (completeLinear n)
  simpa only [productSpan, square, Submodule.mem_top, true_and, completeProduct] using hh.trans hr

private theorem complete_square (n : ℕ) (i : Fin n) :
    completeProduct n (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) i) =
      fun j => (if j=i then 1 else 0) + 1 := by
  classical
  ext j
  simp [completeProduct,coordinateProduct,completeLinear,Pi.basisFun_apply,Pi.single_apply]

private theorem complete_support (n : ℕ) (i j : Fin n) :
    supportRelation (completeProduct n) (Pi.basisFun ℂ (Fin n)) i j := by
  classical
  change (Pi.basisFun ℂ (Fin n)).equivFun
    (completeProduct n (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) i)) j ≠ 0
  rw [complete_square]
  simp only [Module.Basis.equivFun_apply, Pi.basisFun_repr]
  split_ifs <;> norm_num

private theorem complete_natural (n : ℕ) : ∀ i j : Fin n, i ≠ j →
    completeProduct n (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) j) = 0 := by
  intro i j hij
  change completeLinear n (_ * _) = 0
  have hz : (Pi.basisFun ℂ (Fin n) i : Coord n)*Pi.basisFun ℂ (Fin n) j = 0 := by
    simpa [Pi.basisFun_apply, Pi.single_apply, hij, Ne.symm hij] using
      (Pi.single_mul_left (α := fun _ : Fin n => ℂ) (i := i)
        (f := Pi.single j (1 : ℂ)) (1 : ℂ)).symm
  rw [hz,map_zero]

private theorem complete_simple {n : ℕ} (hn : 1 ≤ n) : IsSimple (completeProduct n) := by
  apply simple_of_connected hn (completeProduct n) (Pi.basisFun ℂ (Fin n))
  · exact complete_natural n
  · exact complete_perfect n
  · intro i j
    exact Relation.ReflTransGen.single (complete_support n i j)

private noncomputable def completeLift {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Aut (completeProduct n) := by
  refine ⟨permutationLinear σ, ?_⟩
  intro x y
  ext j
  simpa [completeProduct, coordinateProduct, completeLinear, permutationLinear,
    LinearMap.sum_apply] using
    congrArg (fun t : ℂ => x (σ.symm j) * y (σ.symm j) + t)
      (Equiv.sum_comp σ.symm (fun i => x i * y i)).symm

private theorem complete_aut_card (n : ℕ) :
    Finite (Aut (completeProduct n)) ∧ Nat.card (Aut (completeProduct n)) = n.factorial := by
  classical
  let μ := completeProduct n
  let b := Pi.basisFun ℂ (Fin n)
  let hb := complete_natural n
  have hp : perfect μ := by
    simpa only [perfect,square,productSpan,Submodule.mem_top,true_and] using complete_perfect n
  let ρ := rho μ b hb hp
  have hρi : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro f hf
    have hh : ρ f = 1 := hf
    obtain ⟨t,ht,hf,he⟩ := (rho_kernel_iff μ b hb hp f).mp hh
    have hone (i : Fin n) : t i = 1 := by
      have h := he i i (complete_support n i i)
      apply mul_left_cancel₀ (ht i)
      simpa [pow_two] using h.symm
    change f = 1
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change f.val (b i) = b i
    simpa only [hone,one_smul] using hf i
  have hρs : Function.Surjective ρ := by
    intro σ
    refine ⟨completeLift σ, ?_⟩
    apply Equiv.ext
    intro i
    let d := monomialData μ b hb hp (completeLift σ)
    change d.perm i = σ i
    have hh := d.image i
    have himage : (completeLift σ).val (b i) = b (σ i) :=
      D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutationLinear_basis σ i
    rw [himage] at hh
    exact (b.linearIndependent.eq_of_smul_apply_eq_smul_apply (1:ℂ) (d.scalar i)
      (σ i) (d.perm i) one_ne_zero (by simpa using hh)).symm
  refine ⟨automorphism_finite μ b hb hp, ?_⟩
  simpa only [Nat.card_perm,Nat.card_fin] using Nat.card_congr (Equiv.ofBijective ρ ⟨hρi,hρs⟩)

private theorem coordinate_simple_bound {n : ℕ} (hn : 1 ≤ n) (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0) (hs : IsSimple μ) :
    Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ max n.factorial (n*(2^n-1)) := by
  classical
  have hp : perfect μ := by
    simpa only [perfect,square,productSpan,Submodule.mem_top,true_and] using simple_perfect μ hs
  let R := supportRelation μ b
  let ho := (support_positive_degrees μ b hb hp).1
  let hi := (support_positive_degrees μ b hb hp).2
  let β := beta R ho hi
  letI := Fintype.ofFinite (Blocks R)
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  haveI : Nonempty (Blocks R) := ⟨project R (Classical.arbitrary (Fin n))⟩
  have hc := connected_beta_cycle R ho hi (simple_support_connected μ b hb hs)
  obtain ⟨σ,hσ⟩ := supported_permutation μ b hb hp
  obtain ⟨k,hk,hnk,hfib⟩ := equal_fibers hn R ho hi hc σ hσ
  let s := Fintype.card (Blocks R)
  have hspos : 1 ≤ s := Fintype.card_pos
  have hn' : n=s*k := by simpa [s,Nat.card_eq_fintype_card] using hnk
  have hbound := automorphism_quotient_bound μ b hb hp
  have heq : cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm (Blocks R)))) *
      (∏ q : Blocks R, (Nat.card (Fiber R q)).factorial) = s*(2^s-1)*k.factorial^s := by
    rw [cycle_weight_single β hc]
    simp only [hfib,Finset.prod_const,Finset.card_univ]
    rfl
  refine ⟨automorphism_finite μ b hb hp, hbound.trans ?_⟩
  change cycleWeight β * _ * _ ≤ _
  rw [heq]
  by_cases h1 : s=1
  · have hkn : k=n := by simpa only [h1,one_mul] using hn'.symm
    simp [h1,hkn]
  by_cases hk1 : k=1
  · have hsn : s=n := by simpa only [hk1,mul_one] using hn'.symm
    simp only [hk1,Nat.factorial_one,one_pow,mul_one,hsn]
    exact le_max_right _ _
  exact (factorial_period_bound s k (by omega) (by omega)).trans
    (by rw [← hn']; exact le_max_left _ _)

private theorem simple_bound {A : Type*} [AddCommGroup A] [Module ℂ A]
    [FiniteDimensional ℂ A] {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 1 ≤ n) (hd : Module.finrank ℂ A = n)
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A)
    (hb : ∀ i j, i ≠ j → μ (b i) (b j) = 0) (hs : IsSimple μ) :
    Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ max n.factorial (n*(2^n-1)) := by
  let bn := dimensionBasis hd b
  let ν := transportProduct bn.equivFun μ
  have hbn := D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport.dimensionBasis_natural hd μ b hb
  have hc := (natural_basis_transport_iff μ bn).mp hbn
  have hsν := simple_transport bn.equivFun μ hs
  have hh := coordinate_simple_bound hn ν (Pi.basisFun ℂ (Fin n)) hc hsν
  haveI : Finite (Aut ν) := hh.1
  haveI : Finite (Aut μ) := Finite.of_equiv (Aut ν) (automorphismConjugacy bn.equivFun μ).toEquiv.symm
  exact ⟨inferInstance, (Nat.card_congr (automorphismConjugacy bn.equivFun μ).toEquiv).trans_le hh.2⟩

private theorem cycle_on_finRotate {n : ℕ} (hn : 1 ≤ n) :
    (finRotate n).IsCycleOn Set.univ := by
  by_cases h2 : 2 ≤ n
  · have hh := (isCycle_finRotate_of_le h2).isCycleOn
    convert hh using 1
    ext i
    simpa using Equiv.Perm.mem_support.mp (show i ∈ (finRotate n).support by
      rw [support_finRotate_of_le h2]; exact Finset.mem_univ i)
  · have hn1 : n=1 := by omega
    subst n
    exact Equiv.Perm.isCycleOn_of_subsingleton _ _

private theorem cyclic_family {n : ℕ} (hn : 1 ≤ n) :
    commutative (permutationProduct (finRotate n)) ∧
    hasNaturalBasis (permutationProduct (finRotate n)) ∧
    IsSimple (permutationProduct (finRotate n)) ∧
    Finite (Aut (permutationProduct (finRotate n))) ∧
    Nat.card (Aut (permutationProduct (finRotate n))) = n*(2^n-1) := by
  classical
  let σ := finRotate n
  have hf := permutation_family σ
  have hc := cycle_on_finRotate hn
  have hp : productSpan (permutationProduct σ) = ⊤ := by
    simpa only [productSpan,perfect,square,Submodule.mem_top,true_and] using hf.2.2.1
  have hsimple : IsSimple (permutationProduct σ) := by
    apply simple_of_connected hn (permutationProduct σ) (Pi.basisFun ℂ (Fin n))
      (D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_mixed σ) hp
    intro i j
    obtain ⟨m,hm⟩ := Equiv.Perm.IsCycleOn.exists_pow_eq' Set.finite_univ hc
      (Set.mem_univ i) (Set.mem_univ j)
    rw [← hm]
    clear hm
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.tail ((D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_support σ _ _).mpr rfl)
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  refine ⟨hf.1,hf.2.1,hsimple,hf.2.2.2.1,?_⟩
  rw [hf.2.2.2.2, ← cycle_weight_centralizer]
  simpa using cycle_weight_single σ hc

theorem result : D5.S3.QuadraticForms.EvolutionAlgebras.SimpleEvolutionAutomorphismMaximum.claim := by
  intro n hn
  constructor
  · intro A _ _ _ ι _ μ b hd hb hcomm hs
    exact simple_bound hn hd μ b hb hs
  · by_cases hmax : n.factorial ≤ n*(2^n-1)
    · have hf := cyclic_family hn
      exact ⟨permutationProduct (finRotate n),Module.finrank_fin_fun ℂ,hf.1,hf.2.1,
        hf.2.2.1,hf.2.2.2.1, hf.2.2.2.2.trans (max_eq_right hmax).symm⟩
    · have hf := complete_aut_card n
      exact ⟨completeProduct n,Module.finrank_fin_fun ℂ,(fun x y => by
        change completeLinear n (x*y) = completeLinear n (y*x); rw [mul_comm]),
        ⟨Pi.basisFun ℂ (Fin n),complete_natural n⟩,
        complete_simple hn,hf.1,hf.2.trans (max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hmax))).symm⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.SimpleEvolutionAutomorphismMaximum
