/- GID: D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cube polynomials satisfy an identity of formal power series with cleared denominators. -/

/-
Declaration classifications after expansion of both same-delivery modules.
amGraph: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amInduceIso, am_cube_iff, cubeCount, cubeCount_eq_card_data, realizeCube, realizeCube_bijective.
cubeCount: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose, cubeCount_eq_card_data, cubePoly, cubePoly_endpoint_sum.
cubePoly: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubePoly_endpoint_sum, cubeSeries, cubeSeries_eq_resolvent, runWeight_partition.
x: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen, amcDen_factor, amcNum, blockNum, blockSeries_cleared, derivative_blockNum, result.
z: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen, amcDen_factor, amcNum, blockDen, blockNum, blockSeries_cleared, claim, derivative_blockDen, derivative_blockNum, geom_z_inverse, marked_resolvent_cleared, result.
amcDen: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen_factor, claim, marked_resolvent_cleared, result.
amcNum: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): claim, result.
cubeSeries: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): claim, cubeSeries_eq_resolvent, result.
claim: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): result.
AMWord: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): EndpointChoices, amInduceIso, am_cube_iff, cubeCount_endpoint_choose, cubeCount_eq_card_data, cubePoly_endpoint_sum, endpointDataEquiv, instFintypeAMWord, instFintypeEndpointChoices, markSigmaEquiv, marked_endpoint_double_count, realize, realizeCube, realizeCube_bijective, realize_wordSet, runWeight, runWeight_above, runWeight_partition, runWeight_zero, wordSet, wordSet_injective.
wordSet: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amInduceIso, am_cube_iff, realizeCube, realizeCube_bijective, realize_wordSet, wordSet_injective.
amInduceIso: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): am_cube_iff.
am_cube_iff: proof_shape: content; reason: Same-delivery coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): realizeCube, realizeCube_bijective.
CubeData: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose, cubeCount_eq_card_data, endpointDataEquiv, instFintypeCubeData, realize, realizeCube, realizeCube_bijective, realize_wordSet.
realize: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): realizeCube, realizeCube_bijective, realize_wordSet.
realize_wordSet: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): realizeCube, realizeCube_bijective.
realizeCube: proof_shape: content; reason: Same-delivery coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cubeCount_eq_card_data, realizeCube_bijective.
wordSet_injective: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): realizeCube_bijective.
realizeCube_bijective: proof_shape: content; reason: Constructs the bijection between induced copies and unique admissible top/direction data. Consumer(s): cubeCount_eq_card_data.
cubeCount_eq_card_data: proof_shape: content; reason: Same-delivery realizeCube_bijective, coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cubeCount_endpoint_choose.
IsEndpoint: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): all_erasures_iff_endpoints, endpointDataEquiv, endpoint_count_le, endpoint_count_raw, endpoint_flip_iff, endpoints, erase_endpoints_admissible, raw_one_endpoint_iff, runWeight_zero.
endpoints: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): EndpointChoices, all_erasures_iff_endpoints, cubeCount_endpoint_choose, cubePoly_endpoint_sum, endpointDataEquiv, endpoint_count_raw, endpoint_count_wordOfTuple, erase_endpoints_admissible, extractMarked_endpoints, instFintypeEndpointChoices, marked_endpoint_double_count, runWeight, runWeight_above, runWeight_partition, runWeight_zero.
raw_one_location: proof_shape: content; reason: Locates each one in a valid circular run block by list decomposition. Consumer(s): endpoint_flip_iff.
raw_one_endpoint_iff: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): endpoint_count_raw, endpoint_flip_iff.
endpoint_flip_iff: proof_shape: content; reason: Same-delivery raw_one_location survives expansion and the normalization bypass test. Consumer(s): all_erasures_iff_endpoints, erase_endpoints_admissible.
erase_false: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): erase_endpoints_admissible.
erase_insert_flip: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): all_erasures_iff_endpoints, erase_endpoints_admissible.
erase_endpoints_admissible: proof_shape: content; reason: Induction proves simultaneous endpoint erasure preserves circular admissibility. Consumer(s): all_erasures_iff_endpoints.
all_erasures_iff_endpoints: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, raw_one_location survives expansion and the normalization bypass test. Consumer(s): endpointDataEquiv.
EndpointChoices: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose, endpointDataEquiv, instFintypeEndpointChoices.
endpointDataEquiv: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, raw_one_location survives expansion and the normalization bypass test. Consumer(s): cubeCount_endpoint_choose.
cubeCount_endpoint_choose: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, raw_one_location, realizeCube_bijective, coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cubePoly_endpoint_sum.
endpoint_count_le: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cubePoly_endpoint_sum.
cubePoly_endpoint_sum: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, raw_one_location, realizeCube_bijective, coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): runWeight_partition.
tupleEndpoints: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): blockSeries_coefficient_tuples, endpointLetter_prod, endpoint_count_raw, endpoint_count_wordOfTuple, extractMarked_endpoints, marked_endpoint_double_count, runWeight_marked_coeff, tupleWeight.
endpoint_count_raw: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): endpoint_count_wordOfTuple.
endpoint_count_wordOfTuple: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): extractMarked_endpoints.
runWeight: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeSeries_eq_resolvent, marked_endpoint_double_count, runWeight_above, runWeight_marked_coeff, runWeight_partition, runWeight_zero.
tupleWeight: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): marked_endpoint_double_count, runWeight_marked_coeff.
markSigmaEquiv: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): marked_endpoint_double_count.
extractMarked_endpoints: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): marked_endpoint_double_count.
marked_endpoint_double_count: proof_shape: content; reason: Establishes the endpoint-weighted marked-boundary counting identity over the common word/tuple realization. Consumer(s): runWeight_marked_coeff.
runWeight_partition: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, raw_one_location, realizeCube_bijective, coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cubeSeries_eq_resolvent.
runWeight_zero: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cubeSeries_eq_resolvent.
blockSeries: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen_factor, blockSeries_cleared, blockSeries_coefficient_tuples, blockSeries_constant, blockSeries_pow_low, block_derivative_cleared, coeff_marked_blocks, cubeSeries_eq_resolvent, endpointLetterPartial_approx, geom_partial_approx, marked_block_coefficient, marked_resolvent_cleared, result, runWeight_marked_coeff.
endpointRunPartial: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): endpointLetterPartial_approx, endpointLetterPartial_explicit, endpointRunPartial_explicit.
endpointLetter: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): blockSeries_coefficient_tuples, endpointLetterPartial, endpointLetterPartial_explicit, endpointLetter_prod.
endpointLetterPartial: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): blockSeries_coefficient_tuples, endpointLetterPartial_approx, endpointLetterPartial_explicit.
endpointRunPartial_explicit: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): endpointLetterPartial_approx.
endpointLetterPartial_explicit: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): endpointLetterPartial_approx.
endpointLetterPartial_approx: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): blockSeries_coefficient_tuples.
agree_pow: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): blockSeries_coefficient_tuples.
endpointLetter_prod: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): blockSeries_coefficient_tuples.
blockSeries_coefficient_tuples: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): runWeight_marked_coeff.
blockSeries_constant: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): blockSeries_pow_low, geom_partial_approx, marked_resolvent_cleared.
blockSeries_pow_low: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): geom_partial_approx.
geom_partial_approx: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): coeff_marked_blocks.
coeff_marked_blocks: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cubeSeries_eq_resolvent.
marked_block_coefficient: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): runWeight_marked_coeff.
runWeight_marked_coeff: proof_shape: content; reason: Same-delivery marked_endpoint_double_count survives expansion and the normalization bypass test. Consumer(s): cubeSeries_eq_resolvent.
runWeight_above: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cubeSeries_eq_resolvent.
coeff_geom_z: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cubeSeries_eq_resolvent.
cubeSeries_eq_resolvent: proof_shape: content; reason: Same-delivery erase_endpoints_admissible, marked_endpoint_double_count, raw_one_location, realizeCube_bijective, coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): result.
blockDen: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen_factor, blockSeries_cleared, block_derivative_cleared, derivative_blockDen, marked_resolvent_cleared, result.
blockNum: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): amcDen_factor, blockSeries_cleared, block_derivative_cleared, derivative_blockNum, result.
geom_z_inverse: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): blockSeries_cleared, result.
blockSeries_cleared: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): amcDen_factor, block_derivative_cleared, result.
amcDen_factor: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): marked_resolvent_cleared.
marked_resolvent_cleared: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): result.
block_derivative_cleared: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): result.
derivative_blockDen: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): result.
derivative_blockNum: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): result.
result: proof_shape: content; reason: After inlining both new modules, the induced-cube, realization-bijection, endpoint-erasure and weighted-count constructions remain on the live path. Consumer(s): external settlement.
instFintypeAMWord: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose, cubePoly_endpoint_sum, instFintypeEndpointChoices, marked_endpoint_double_count, realize, realize_wordSet, runWeight, runWeight_above, runWeight_partition, runWeight_zero.
instFintypeCubeData: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose, cubeCount_eq_card_data.
instFintypeEndpointChoices: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cubeCount_endpoint_choose.
instFintypeMarkedWords: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): marked_endpoint_double_count.
escape_witness: realizeCube_bijective, raw_one_location, erase_endpoints_admissible, marked_endpoint_double_count; each survives the frozen-fact normalization bypass test.
admission_basis: open-problem-resolution (#14961; Proved)
Direct frozen dependencies of result: D5/S1/Ledger/BoundedTimeSlice.TailBox declaration statement_id sha256:620077c2b062d7fe99c8f2b63a7de76d46b66b50be885158d6789d33674e0286; D5/S1/Words/AssociatedMersenne/CircularWords.Admissible declaration statement_id sha256:550bebdacb063efbccb884c39bfe027a139ef17485aa770fa0f126f05bf3abff; D5/S1/Words/AssociatedMersenne/CircularWords.IsMarkedStart declaration statement_id sha256:cb0e0be155bb65e5e10ee03b8ee7cb42b2cb285299de1430572a0887d4936aa4; D5/S1/Words/AssociatedMersenne/CircularWords.admissible_nonzero_has_marked_start declaration statement_id sha256:cbadc6992029df81d9496eb41f97ca4e249d51641decf50fa8be5a9a79dcfadf; D5/S1/Words/AssociatedMersenne/CircularWords.card_marks declaration statement_id sha256:8ff09007257142e24b8afdba3eb95f8ba5b7cbf0cf26635e4da70fb08bb9fc11; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd declaration statement_id sha256:5e9c7a6e688289ccf418da167543c88bb2646f479cf1a66449ba381b9302d171; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_assoc declaration statement_id sha256:c17369ee6b8af6d4c1dd11b88560b2273d8fb8d634092534cf9c3bf8451b91c9; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_bijective declaration statement_id sha256:d316dc22242e63047868708c567588692886cfb19bec9677c7554cb016d1793d; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_offset declaration statement_id sha256:62f46cf1b77c4ec2b3b483db7c6eadcab60a211713a70921b1f83073bbcb9f67; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_predecessor_pos declaration statement_id sha256:533d02c91138cac2b66756eb146a56136bf43dc771222c71a08ddf92af133475; D5/S1/Words/AssociatedMersenne/CircularWords.cycAdd_zero declaration statement_id sha256:7b0f3f46e6d6c6c7a51698648b7152e11268092573257b83ee550e8261745052; D5/S1/Words/AssociatedMersenne/CircularWords.cycSub declaration statement_id sha256:0b7dfafc3a684b4f7170ca4bbec55bde67c595f79b0c9e189e740db162e810b4; D5/S1/Words/AssociatedMersenne/CircularWords.flip declaration statement_id sha256:da03509aacd554badb640926b8d037aaaa37e76e34c3290a3a2faf4ab3d5179e; D5/S1/Words/AssociatedMersenne/CircularWords.linearize declaration statement_id sha256:9573fe33b3b449b2636064f62eb15cf485b2997fbae4d1bca41de662882c99ee; D5/S1/Words/AssociatedMersenne/CircularWords.linearize_length declaration statement_id sha256:93ccfa762f8083732d90def5f62baab3df43b732d2e77b7312d29361606ef9b9; D5/S1/Words/AssociatedMersenne/CircularWords.linearize_move_mark declaration statement_id sha256:b475c4e053eaa2f7214336c85d46222732949b41fe4cb60897ef658ebafac5b7; D5/S1/Words/AssociatedMersenne/CircularWords.marked_start_predecessor declaration statement_id sha256:b6902e14f628cd9c0ff475624fc7baa43cb7b0e6baefec32e36631634737c7e7; D5/S1/Words/AssociatedMersenne/CircularWords.offset declaration statement_id sha256:44726df04b6e89fcf99de45f29f73eba8b071f2c8376c96c4e9c9883539916e5; D5/S1/Words/AssociatedMersenne/CircularWords.offset_lt declaration statement_id sha256:406e9ee0865b5647799d0338f751074b0310d1188d303447dc2713edd1c1e010; D5/S1/Words/AssociatedMersenne/CircularWords.runCount declaration statement_id sha256:1b328d4f61315b2f0acbf90e1f0be56332317882068907b61e55efd16621b520; D5/S1/Words/AssociatedMersenne/CircularWords.zero_admissible declaration statement_id sha256:d4e307992c7b939d3506fcb4b54fa537a8de5688108a6686b675573b064410f8; D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.instFintypeRunTuples declaration statement_id sha256:fe322ce49e4753faceeac79f07d7d8d915728aa6125cfec10e901c047cedacb2; D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_le declaration statement_id sha256:8a7b4e3e420132893b673d261812677f9d82d0cc8018e76a5f984d7f77c678c7; D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_zero_iff declaration statement_id sha256:41c0f13a277f40d631fae68c674838917b223b69c4c664969bc463caf3124da9; D5/S1/Words/AssociatedMersenne/MultiRunDegrees.linearize_at_pair declaration statement_id sha256:4c71cdc8a2c6c3c8faee8c18bf24251a89ccc08a0b65e64ed758f71110345bdf; D5/S1/Words/AssociatedMersenne/MultiRunDegrees.raw_coordinate_sum declaration statement_id sha256:adfb6886991cd75764dcf5dc4669c246bef3614781f7214f45dc833bac52d7ca; D5/S1/Words/AssociatedMersenne/MultiRunDegrees._proof_1 declaration statement_id sha256:a7f88fa9562fd998470e0b0ceb29b0eb40caad7d729b7a081056c527abced23a; D5/S1/Words/AssociatedMersenne/MultiRunDegrees.raw_one_delete_iff declaration statement_id sha256:37f68e0d735c69cf4f61bda02220c082541c645520ade380d34ce47df105ed4b; D5/S1/Words/AssociatedMersenne/MultiRunDegrees.run_endpoint_sum declaration statement_id sha256:0929afb7b00829a8bab62c33cb3c1a0a658735c94a9e4b501600020206381381; D5/S1/Words/AssociatedMersenne/RunTupleBijection.GoodTuple declaration statement_id sha256:ce3c80cdc3ce79dc1546e693bb6db1253f077424b11e9604ebb9adbbce86c9e5; D5/S1/Words/AssociatedMersenne/RunTupleBijection.MarkedWords declaration statement_id sha256:521e4ec9f4294685c435492a4ab910b327d69580cf833537bda984880bc3b70a; D5/S1/Words/AssociatedMersenne/RunTupleBijection.RunTuples declaration statement_id sha256:1ebf2b5b46716c8dc5e8cdcfb98040ef5c808bbdd28f25c267fe08b9e981fd9a; D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractListTuple declaration statement_id sha256:c5c73d312d46ad980f7274966b25688f332e9cd72e32aa3ddf072b8b60c0ddcd; D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked declaration statement_id sha256:436caabe04a400869081a1cc3f8e8fd4d1d7c586dce6af283d9dc199fa14b723; D5/S1/Words/AssociatedMersenne/RunTupleBijection.extractMarked_runs declaration statement_id sha256:064a0ed5188aeaec5b0988c414ec44249117ae91b2b1b4eec975888d12a50f5c; D5/S1/Words/AssociatedMersenne/RunTupleBijection.instFintypeGoodTuple declaration statement_id sha256:10b09991e98034450384b2b2708047ad601b91bd9b02c142ef891ccaf3cf39bd; D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_get_optional declaration statement_id sha256:30e121ae227694d60207214f4375f9a14a64b906bfb4265f151c22f75a1144d4; D5/S1/Words/AssociatedMersenne/RunTupleBijection.linearize_wordOfTuple declaration statement_id sha256:c76fbf21f9b57178609af01f38690dfc864630080c6555012ba6db6fb1b59c65; D5/S1/Words/AssociatedMersenne/RunTupleBijection.markedTupleEquiv declaration statement_id sha256:7acdd7df24c5989f225430d2f907213f62296b745f9963168e941571a67ce484; D5/S1/Words/AssociatedMersenne/RunTupleBijection.marked_admissible_tuple declaration statement_id sha256:ba29c1c87b854b9f691f78d7e6ec0d24cadc2469aa7e24218a1e25e09541b20d; D5/S1/Words/AssociatedMersenne/RunTupleBijection.pairPrefix declaration statement_id sha256:9512d25c1db0756f20394d113ec407c8d27e14b01a330cfaa4802d2766489463; D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawPairs declaration statement_id sha256:ee8f2492eedf96031bc3839ffbffa24b029e8c6ef96fa0d5765c9d7896b6f0fc; D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord declaration statement_id sha256:20ed513295ffb7cc9095d0029cab0ce9a4ae3c43f96bf28d80a7a5672301e06f; D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_append declaration statement_id sha256:8ede45febf74df81515883452ab2e9b979dcb5418f1c27cce492e369228a279e; D5/S1/Words/AssociatedMersenne/RunTupleBijection.rawWord_cons declaration statement_id sha256:396da8cfa3653ace9b04e2919b2c1324e697c698a272885e7e9b0a7c6b2b0520; D5/S1/Words/AssociatedMersenne/RunTupleBijection.raw_encoding_marked declaration statement_id sha256:ece2b7858e26a48d9aeeab822406ac6ff39a2febf16cfca1586c404896f183df; D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList declaration statement_id sha256:b044b10ae698fa80d7193d19c0a982d4314e38c64019b0086ff4cbbecffc3bf9; D5/S1/Words/AssociatedMersenne/RunTupleBijection.tupleList_eq_rawPairs declaration statement_id sha256:a3e8bfdf85e01c4221d8654f390e24847a2171f782182181bf0c7a66faa1e21c; D5/S1/Words/AssociatedMersenne/RunTupleBijection.wordOfTuple declaration statement_id sha256:842d93475c308058c85db51f964a4a12734c5b596ac9b531dd6f61af45b3cefe; D5/S1/Words/AssociatedMersenne/TransferResolvent.coeff_euler declaration statement_id sha256:ff266700dbba12167cf0dcf43368cfd314148d76526f135aa0783df7620cd300; D5/S1/Words/AssociatedMersenne/TransferTuples.AgreeUpTo declaration statement_id sha256:48def4c305570b5d4a4c36a9f1337df038a637bbcea1ae38e851ab39079c2214; D5/S1/Words/AssociatedMersenne/TransferTuples.add declaration statement_id sha256:e7550a4c39963495dfd54196ac28ae0b89bed1e06061640a273a1333e8c4730d; D5/S1/Words/AssociatedMersenne/TransferTuples.mul declaration statement_id sha256:77f047f5cbcbe127cd90bdb0447a34cf915d4d7f043e913ffffddc6431e3b9de; D5/S1/Words/AssociatedMersenne/TransferTuples.alphabetPair declaration statement_id sha256:4ca9154414e096618f9b10206ed21be1fe8df877102d482c86c97ce233f916d4; D5/S1/Words/AssociatedMersenne/TransferTuples.boundedList declaration statement_id sha256:7cbe7d95032f80b72a1215ef0b4cdb11663092c30cf3a5d8e5ff4247904ad040; D5/S1/Words/AssociatedMersenne/TransferTuples.bounded_weight_sum declaration statement_id sha256:b70d524a90a277720816a8e47c6006414ebd21bc91694a74e7eec7cfc5337f80; D5/S1/Words/AssociatedMersenne/TransferTuples.geom declaration statement_id sha256:01a1223a2e5e6e5a5229e54ad05b1db01a891fcee76a6acf60f5a7e91fd2bf79; D5/S1/Words/AssociatedMersenne/TransferTuples.geom_X2 declaration statement_id sha256:462470f8ac107e6fc2cdde03ca91d6ef3d139ad9e4a63eecb689c3e7b15221a4; D5/S1/Words/AssociatedMersenne/TransferTuples.geom_finite_identity declaration statement_id sha256:d44d24f3a10914022d8c82d96423812e0f0ca4d25ccc4e18fac64d6b7e53c8bb; D5/S1/Words/AssociatedMersenne/TransferTuples.geom_monomial_approx declaration statement_id sha256:d93942810787992d3986ba1563a1b3b49a331be74e7f924a61cf6f7f3f347161; D5/S1/Words/AssociatedMersenne/TransferTuples.geom_mul declaration statement_id sha256:c7f9acea43daf9b5f44b3eceb454a9a2f0b4b8ba42ce0a26a13cefdc50533dd1; D5/S1/Words/AssociatedMersenne/TransferTuples.transferLength declaration statement_id sha256:a6bceb5221a7b1249b4be21c0a6870928388fcc8213dfbccc2ed9ac19785e69d; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding declaration statement_id sha256:a382277d81d40c7eb5f352799d8c10bdde5b5649714064ff9e0885d7d67fdbe7; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.map_unitEdge declaration statement_id sha256:767b7fc5a4102b476eb54cecb7fe3e0a06d112370bb9a3b3394d7d150612f373; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.mk declaration statement_id sha256:e4c3d965229119470ae5f69ebb1e015ad2684edfa8fbe6d18bba0de6eb334fad; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.toFun declaration statement_id sha256:3e37a2305777f9f61aa663652629c9c460a1bdcafa91439d6f2bc062cd4ed071; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge declaration statement_id sha256:457db4d7949335f6c43fa28b765a322e169ba2b8122789fc1c0ea9a2007fe639; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer declaration statement_id sha256:756a195ca04f1f89025d96b4fa6b88f2e91e02baca9fc208167fffe1994b895d; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour declaration statement_id sha256:abe4bfcc54e3a0011447fcd2c82806ae732c85e31b1a12547da2b525b09c211c; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise declaration statement_id sha256:6a4867e887abad6d640d288504030c6930ab4631bcd86fa3d882216fcbabed43; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity._proof_1 declaration statement_id sha256:a0d1eec21077c6eec5b3e628b462854a639d42698e64694f38657df573238a25; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour declaration statement_id sha256:ea64aea534233b0857077988bfc0b75da4e3471c43ee925e69dc824648c33e9c; D5/S3/Combinatorics/Graph/Hypercube.hypercube declaration statement_id sha256:e70c1ce92111881fa6bcced6ddb8eeb908912e4c390ec989d4c1880ebc362345.
Same-delivery content dependency: InducedSubcubes.induced_cube_iff; its declarations are expanded in every classification above.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15283; typed realization and sensitivity evidence is not supplied.
-/

import D5.S1.Words.AssociatedMersenne.TransferResolvent
import D5.S3.Combinatorics.Hamming.InducedSubcubes

namespace D5.S3.Combinatorics.Hamming.AssociatedMersenneCubePolynomial

open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Hamming.InducedSubcubes
open D5.S1.Words.AssociatedMersenne
open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S1.Words.AssociatedMersenne.MultiRunDegrees
open D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration
open D5.S1.Words.AssociatedMersenne.TransferTuples
open D5.S1.Words.AssociatedMersenne.TransferResolvent
open Classical
open scoped BigOperators
noncomputable section


/- ===== Statements ===== -/

open D5.S1.Words.AssociatedMersenne.CircularWords
open scoped BigOperators

def amGraph (n : ℕ) : SimpleGraph {w : Fin n → Bool // Admissible w} :=
  (hypercube n).induce {w | Admissible w}

noncomputable def cubeCount (n k : ℕ) : ℕ :=
  Nat.card {S : Finset {w : Fin n → Bool // Admissible w} //
    Nonempty ((amGraph n).induce (S : Set _) ≃g hypercube k)}

noncomputable def cubePoly (n : ℕ) : Polynomial ℕ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (cubeCount n k)

def x : PowerSeries (Polynomial ℤ) := PowerSeries.C Polynomial.X

def z : PowerSeries (Polynomial ℤ) := PowerSeries.X

def amcDen : PowerSeries (Polynomial ℤ) :=
  1 - z - z^2 - x*z^3 - x*(1+x)*z^5

def amcNum : PowerSeries (Polynomial ℤ) :=
  z + 2*z^2 + 3*x*z^3 + 5*x*(1+x)*z^5

def cubeSeries : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => if n = 0 then 0 else (cubePoly n).map (Nat.castRingHom ℤ)

def claim : Prop :=
  cubeSeries * (1 - z^2) * amcDen = amcNum * (1 - z^2) - 2*z^2*amcDen



/- ===== CubeEnumeration ===== -/

open D5.S1.Words.AssociatedMersenne.CircularWords
open Classical
set_option maxHeartbeats 3000000

private abbrev AMWord (n : ℕ) := {w : Fin n → Bool // Admissible w}

private instance (n : ℕ) : Fintype (AMWord n) := Fintype.ofFinite _

private def wordSet {n : ℕ} (A : Finset (AMWord n)) : Set (Fin n → Bool) :=
  {w | ∃ a ∈ A, a.val = w}

private def amInduceIso {n : ℕ} (A : Finset (AMWord n)) :
    (amGraph n).induce (A : Set _) ≃g (hypercube n).induce (wordSet A) := by
  let f : {a : AMWord n // a ∈ A} → wordSet A := fun a =>
    ⟨a.val.val, ⟨a.val, a.property, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : wordSet A => w.val) h
  have hsurj : Function.Surjective f := by
    rintro ⟨w, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  exact { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_rel_iff' := by intros; rfl }

private theorem am_cube_iff {n k : ℕ} (A : Finset (AMWord n)) :
    Nonempty ((amGraph n).induce (A : Set _) ≃g hypercube k) ↔
    ∃! p : (Fin n → Bool) × Finset (Fin n),
      p.2.card = k ∧ p.2 ⊆ (Finset.univ.filter (fun q => p.1 q = true)) ∧ wordSet A = downCube p.1 p.2 := by
  rw [← induced_cube_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨(amInduceIso A).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(amInduceIso A).trans e⟩

private def CubeData (n k : ℕ) :=
  {p : (Fin n → Bool) × Finset (Fin n) //
    p.2.card = k ∧ p.2 ⊆ (Finset.univ.filter (fun q => p.1 q = true)) ∧ ∀ T ⊆ p.2, Admissible (erase p.1 T)}

private instance (n k : ℕ) : Fintype (CubeData n k) := by
  unfold CubeData
  exact Fintype.ofFinite _

private def realize {n k : ℕ} (p : CubeData n k) : Finset (AMWord n) :=
  Finset.univ.filter (fun w => w.val ∈ downCube p.val.1 p.val.2)

private theorem realize_wordSet {n k : ℕ} (p : CubeData n k) :
    wordSet (realize p) = downCube p.val.1 p.val.2 := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨T, hT, rfl⟩
    refine ⟨⟨erase p.val.1 T, p.property.2.2 T hT⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T, hT, rfl⟩

private def realizeCube {n k : ℕ} (p : CubeData n k) :
    {A : Finset (AMWord n) // Nonempty ((amGraph n).induce (A : Set _) ≃g hypercube k)} := by
  refine ⟨realize p, (am_cube_iff (realize p)).mpr ?_⟩
  refine ⟨p.val, ⟨p.property.1, p.property.2.1, realize_wordSet p⟩, ?_⟩
  intro q hq
  exact Prod.ext_iff.mpr (downCube_unique q.1 p.val.1 q.2 p.val.2 hq.2.1 p.property.2.1
    (hq.2.2.symm.trans (realize_wordSet p)))

private theorem wordSet_injective {n : ℕ} : Function.Injective (@wordSet n) := by
  intro A B h
  ext a
  have hh := Set.ext_iff.mp h a.val
  have hf (C : Finset (AMWord n)) : a.val ∈ wordSet C ↔ a ∈ C := by
    constructor
    · rintro ⟨b, hb, hval⟩
      exact (Subtype.ext hval : b = a) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  simpa only [hf] using hh

private theorem realizeCube_bijective {n k : ℕ} : Function.Bijective (@realizeCube n k) := by
  constructor
  · intro p q h
    apply Subtype.ext
    have hA : realize p = realize q := congrArg Subtype.val h
    have hU : downCube p.val.1 p.val.2 = downCube q.val.1 q.val.2 := by
      rw [← realize_wordSet p, ← realize_wordSet q, hA]
    exact Prod.ext_iff.mpr (downCube_unique _ _ _ _ p.property.2.1 q.property.2.1 hU)
  · intro A
    obtain ⟨p, hp, _⟩ := (am_cube_iff A.val).mp A.property
    have hall : ∀ T ⊆ p.2, Admissible (erase p.1 T) := by
      intro T hT
      have hm : erase p.1 T ∈ wordSet A.val := hp.2.2.symm ▸ ⟨T, hT, rfl⟩
      obtain ⟨w, hw, hval⟩ := hm
      exact hval ▸ w.property
    let q : CubeData n k := ⟨p, hp.1, hp.2.1, hall⟩
    refine ⟨q, Subtype.ext ?_⟩
    apply wordSet_injective
    exact (realize_wordSet q).trans hp.2.2.symm

private theorem cubeCount_eq_card_data (n k : ℕ) : cubeCount n k = Fintype.card (CubeData n k) := by
  unfold cubeCount
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective (@realizeCube n k) realizeCube_bijective)).symm



/- ===== EndpointDeletion ===== -/

open D5.S1.Words.AssociatedMersenne
open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open Classical
set_option maxHeartbeats 3000000

private def IsEndpoint {n : ℕ} (w : Fin n → Bool) (q : Fin n) : Prop :=
  w q = true ∧ (w (cycSub q 1) = false ∨ w (cycAdd q 1) = false)

private def endpoints {n : ℕ} (w : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (IsEndpoint w)

-- The locations of one bits in the existing raw circular block encoding.
private theorem raw_one_location (t : List (ℕ × ℕ)) (j : ℕ)
    (hj : j < (rawWord t).length) (hbit : (rawWord t)[j]? = some true) :
    ∃ u r z v p, t = u ++ (r,z) :: v ∧
      j = (rawWord u).length + p ∧ p < r := by
  induction t generalizing j with
  | nil => simp [rawWord] at hj
  | cons b t ih =>
    by_cases hjr : j < b.1
    · exact ⟨[], b.1, b.2, t, j, by simp, by simp [rawWord], hjr⟩
    · have hjz : ¬ j - b.1 < b.2 := by
        intro hjz
        simp [rawWord_cons, List.getElem?_append, hjr, hjz] at hbit
      have hlen : j - (b.1+b.2) < (rawWord t).length := by
        simp only [rawWord_cons, List.length_append, List.length_replicate] at hj
        omega
      have hbit' : (rawWord t)[j-(b.1+b.2)]? = some true := by
        simpa [rawWord_cons, List.getElem?_append, hjr, hjz, Nat.sub_sub] using hbit
      obtain ⟨u,r,z,v,p,ht,hj',hp⟩ := ih _ hlen hbit'
      refine ⟨b::u,r,z,v,p,by simp [ht],?_,hp⟩
      simp only [rawWord_cons, List.length_append, List.length_replicate]
      omega

-- Endpoint neighbourhood readings inside a positive first raw block.
private theorem raw_one_endpoint_iff {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (r z p : ℕ) (t : List (ℕ × ℕ)) (hr : 0 < r) (hz : r < z) (hp : p < r)
    (ht : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) :
    IsEndpoint w (cycAdd i p) ↔ p = 0 ∨ p+1 = r := by
  have hlen : n = r+z+(rawWord t).length := by
    have hh := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using hh
  have read (j : ℕ) (hj : j < r+z) :
      w (cycAdd i j) = if j < r then true else false := by
    have hh := linearize_get_optional w i j (by omega)
    rw [he, rawWord_cons] at hh
    by_cases h : j < r <;>
      simpa [List.getElem?_append, h, show j-r < z by omega] using hh
  have hm : IsMarkedStart w i := raw_encoding_marked w i ((r,z)::t) (by simp)
    (by intro b hb; rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hr, by omega⟩
        · have hh := ht b hb; exact ⟨hh.1, by omega⟩) he
  have hpbit : w (cycAdd i p) = true := by simpa [hp] using read p (by omega)
  have hnext : w (cycAdd (cycAdd i p) 1) = false ↔ p+1 = r := by
    rw [cycAdd_assoc, read (p+1) (by omega)]
    by_cases h : p+1 < r <;> simp [h] <;> omega
  have hprev : w (cycSub (cycAdd i p) 1) = false ↔ p = 0 := by
    by_cases hp0 : p = 0
    · subst p
      simp [cycAdd_zero, marked_start_predecessor hm]
    · rw [cycAdd_predecessor_pos i p (by omega), read (p-1) (by omega)]
      simp [show p-1 < r by omega, hp0]
  simp only [IsEndpoint, hpbit, true_and, hprev, hnext]

private theorem endpoint_flip_iff {n : ℕ} (w : Fin n → Bool) (ha : Admissible w)
    (q : Fin n) (hq : w q = true) :
    Admissible (flip w q) ↔ IsEndpoint w q := by
  obtain ⟨i,hi⟩ := admissible_nonzero_has_marked_start w ha ⟨q,hq⟩
  obtain ⟨t,hne,hp,hlen,he,_⟩ := marked_admissible_tuple w i ha hi
  let raw := rawPairs t
  have heRaw : linearize w i = rawWord raw := by rw [← tupleList_eq_rawPairs]; exact he.symm
  have hraw : ∀ b ∈ raw, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp c hc, by omega⟩
  let j := offset i q
  have hj : j < (rawWord raw).length := by rw [← heRaw, linearize_length]; exact offset_lt i q
  have hbit : (rawWord raw)[j]? = some true := by
    rw [← heRaw, linearize_get_optional w i j (offset_lt i q), cycAdd_offset, hq]
  obtain ⟨u,r,z,v,p,ht,hjp,hpr⟩ := raw_one_location raw j hj hbit
  have hb : (r,z) ∈ raw := by rw [ht]; simp
  have hr := (hraw (r,z) hb).1
  have hz := (hraw (r,z) hb).2
  let a := cycAdd i (rawWord u).length
  have hrot : linearize w a = rawWord ((r,z)::(v++u)) := by
    rw [linearize_move_mark, heRaw, ht, rawWord_append, List.rotate_append_length_eq,
      ← rawWord_append]
    rfl
  have hpRot : ∀ b ∈ v++u, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    apply hraw
    rw [ht]
    simp only [List.mem_append, List.mem_cons] at hb ⊢
    tauto
  have hqpos : q = cycAdd a p := by
    rw [show cycAdd a p = cycAdd i ((rawWord u).length+p) by exact cycAdd_assoc _ _ _]
    rw [← hjp]
    exact (cycAdd_offset i q).symm
  rw [hqpos]
  exact (raw_one_delete_iff w a r z p (v++u) hr hz hpr hpRot hrot).trans
    (raw_one_endpoint_iff w a r z p (v++u) hr hz hpr hpRot hrot).symm

private theorem erase_false {n : ℕ} (w : Fin n → Bool) (S : Finset (Fin n)) (q : Fin n)
    (hq : w q = false) : erase w S q = false := by
  simp [erase, hq]

private theorem erase_insert_flip {n : ℕ} (w : Fin n → Bool) (S : Finset (Fin n)) (q : Fin n)
    (hqS : q ∉ S) (hq : w q = true) :
    erase w (insert q S) = flip (erase w S) q := by
  funext j
  by_cases hj : j = q
  · subst j
    simp [erase, CircularWords.flip, hqS, hq]
  · simp [erase, CircularWords.flip, Function.update_of_ne hj, hj]

/-- Any subset of run endpoints may be removed simultaneously. -/
private theorem erase_endpoints_admissible {n : ℕ} (w : Fin n → Bool) (ha : Admissible w)
    (S : Finset (Fin n)) (hS : S ⊆ endpoints w) : Admissible (erase w S) := by
  induction S using Finset.induction_on with
  | empty => simpa using ha
  | @insert q S hqS ih =>
    have hq : IsEndpoint w q := (Finset.mem_filter.mp (hS (Finset.mem_insert_self _ _))).2
    have hs : S ⊆ endpoints w := fun j hj => hS (Finset.mem_insert_of_mem hj)
    have hsAdm : Admissible (erase w S) := ih hs
    have hqbit : erase w S q = true := by simp [erase, hqS, hq.1]
    have hqnew : IsEndpoint (erase w S) q := by
      refine ⟨hqbit, hq.2.imp (erase_false w S _) (erase_false w S _)⟩
    rw [erase_insert_flip w S q hqS hq.1]
    exact (endpoint_flip_iff (erase w S) hsAdm q hqbit).mpr hqnew

/-- Admissible coordinate subcubes are exactly subsets of the original run endpoints. -/
private theorem all_erasures_iff_endpoints {n : ℕ} (w : Fin n → Bool) (ha : Admissible w)
    (S : Finset (Fin n)) (hS : S ⊆ (Finset.univ.filter (fun q => w q = true))) :
    (∀ T ⊆ S, Admissible (erase w T)) ↔ S ⊆ endpoints w := by
  constructor
  · intro hall q hq
    have hwq : w q = true := (Finset.mem_filter.mp (hS hq)).2
    have hsingle := hall {q} (by simpa)
    have heq : erase w {q} = flip w q := by
      simpa using erase_insert_flip w ∅ q (by simp) hwq
    rw [heq] at hsingle
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (endpoint_flip_iff w ha q hwq).mp hsingle⟩
  · intro hS T hT
    exact erase_endpoints_admissible w ha T (hT.trans hS)



/- ===== EndpointWeight ===== -/

open D5.S1.Words.AssociatedMersenne.CircularWords
open Classical
open scoped BigOperators
set_option maxHeartbeats 3000000

private abbrev EndpointChoices (n k : ℕ) :=
  (w : AMWord n) × {S : Finset (Fin n) // S ⊆ endpoints w.val ∧ S.card = k}

private def endpointDataEquiv (n k : ℕ) : CubeData n k ≃ EndpointChoices n k where
  toFun p := by
    have ha : Admissible p.val.1 := by simpa using p.property.2.2 ∅ (Finset.empty_subset _)
    exact ⟨⟨p.val.1, ha⟩, ⟨p.val.2,
      (all_erasures_iff_endpoints p.val.1 ha p.val.2 p.property.2.1).mp p.property.2.2,
      p.property.1⟩⟩
  invFun p := by
    have hsup : p.2.val ⊆ (Finset.univ.filter (fun q => p.1.val q = true)) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (p.2.property.1 hq)).2.1⟩
    exact ⟨(p.1.val,p.2.val), p.2.property.2, hsup,
      (all_erasures_iff_endpoints p.1.val p.1.property p.2.val hsup).mpr p.2.property.1⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

private instance (n k : ℕ) : Fintype (EndpointChoices n k) := inferInstance

private theorem cubeCount_endpoint_choose (n k : ℕ) :
    cubeCount n k = ∑ w : AMWord n, (endpoints w.val).card.choose k := by
  rw [cubeCount_eq_card_data, Fintype.card_congr (endpointDataEquiv n k), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w hw
  have hcard := Fintype.card_of_subtype ((endpoints w.val).powersetCard k)
    (fun S => Finset.mem_powersetCard)
  exact hcard.trans (Finset.card_powersetCard k _)

private theorem endpoint_count_le {n : ℕ} (w : Fin n → Bool) : (endpoints w).card ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

/-- The cube polynomial is the endpoint-weighted admissible vertex sum. -/
private theorem cubePoly_endpoint_sum (n : ℕ) :
    cubePoly n = ∑ w : AMWord n, (1 + Polynomial.X) ^ (endpoints w.val).card := by
  apply Polynomial.ext
  intro j
  simp only [cubePoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_one_add_X_pow]
  by_cases hj : j < n+1
  · rw [Finset.sum_eq_single j]
    · simp [cubeCount_endpoint_choose]
    · intro b hb hbj
      simp [hbj]
    · simp [Finset.mem_range, hj]
  · have hjn : n < j := by omega
    have hz : ∀ w : AMWord n, (endpoints w.val).card.choose j = 0 := by
      intro w
      exact Nat.choose_eq_zero_of_lt ((endpoint_count_le w.val).trans_lt hjn)
    simp_rw [hz]
    simp only [Nat.cast_zero,Finset.sum_const_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by have := Finset.mem_range.mp hk; omega
    simp [hkj]



/- ===== EndpointTupleCount ===== -/

open D5.S1.Words.AssociatedMersenne
open CircularWords RunTupleBijection MultiRunDegrees
open Classical
open scoped BigOperators
set_option maxHeartbeats 3000000

private def tupleEndpoints (t : List (ℕ × ℕ)) : ℕ := (t.map (fun b => min b.1 2)).sum

/-- Each positive circular block contributes one endpoint for a singleton run, two otherwise. -/
private theorem endpoint_count_raw {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (t : List (ℕ × ℕ)) (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord t) : (endpoints w).card = tupleEndpoints t := by
  have hlen : n = (rawWord t).length := by
    have hh := congrArg List.length he
    simpa [linearize_length] using hh
  have hsum : (endpoints w).card =
      ∑ j ∈ Finset.range n, if IsEndpoint w (cycAdd i j) then 1 else 0 := by
    unfold endpoints
    rw [show (Finset.univ.filter (IsEndpoint w)).card =
      ∑ q : Fin n, if IsEndpoint w q then (1:ℕ) else 0 by simp]
    rw [← Fin.sum_univ_eq_sum_range]
    symm
    exact Equiv.sum_comp (Equiv.ofBijective (fun j : Fin n => cycAdd i j.val)
      (cycAdd_bijective i)) (fun q => if IsEndpoint w q then (1:ℕ) else 0)
  rw [hsum]
  conv_lhs => arg 1; rw [hlen]
  rw [raw_coordinate_sum]
  have hlocal (p : Fin t.length) :
      (∑ j ∈ Finset.range (t[p.val].1+t[p.val].2),
        if IsEndpoint w (cycAdd i (pairPrefix t p.val+j)) then (1:ℕ) else 0) =
        min t[p.val].1 2 := by
    let a := cycAdd i (pairPrefix t p.val)
    let r := t[p.val].1
    let z := t[p.val].2
    have hb := hp t[p.val] (List.getElem_mem p.isLt)
    obtain ⟨u, hrot⟩ : ∃ u, t.rotate p.val = t[p.val] :: u := by
      refine ⟨(t.drop (p.val+1)) ++ t.take p.val, ?_⟩
      rw [List.rotate_eq_drop_append_take (Nat.le_of_lt p.isLt),
        List.drop_eq_getElem_cons p.isLt, List.cons_append]
    have henc : linearize w a = rawWord ((r,z)::u) := by
      rw [linearize_at_pair w i t he p, hrot]
    have hpu : ∀ b ∈ u, 0 < b.1 ∧ b.1 < b.2 := by
      intro b hbu
      apply hp
      have hh : b ∈ t.rotate p.val := by rw [hrot]; simp [hbu]
      exact (List.rotate_perm t p.val).mem_iff.mp hh
    rw [Finset.sum_range_add]
    have hzsum : (∑ j ∈ Finset.range z,
        if IsEndpoint w (cycAdd i (pairPrefix t p.val+(r+j))) then (1:ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hbit : w (cycAdd a (r+j)) = false := by
        have hnn : r+j < n := by
          have hh := congrArg List.length henc
          simp only [linearize_length, rawWord_cons, List.length_append, List.length_replicate] at hh
          have := Finset.mem_range.mp hj
          omega
        have hh := linearize_get_optional w a (r+j) hnn
        rw [henc, rawWord_cons] at hh
        simpa [List.getElem?_append, show ¬r+j < r by omega,
          show r+j-r = j by omega, Finset.mem_range.mp hj] using hh
      have hnot : ¬ IsEndpoint w (cycAdd i (pairPrefix t p.val+(r+j))) := by
        rw [← cycAdd_assoc]
        exact fun h => Bool.noConfusion (hbit.symm.trans h.1)
      simp [hnot]
    rw [hzsum, add_zero]
    have hone : (∑ j ∈ Finset.range r,
        if IsEndpoint w (cycAdd i (pairPrefix t p.val+j)) then (1:ℕ) else 0) =
      ∑ j ∈ Finset.range r, if j = 0 ∨ j+1 = r then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← cycAdd_assoc,
        raw_one_endpoint_iff w a r z j u hb.1 hb.2 (Finset.mem_range.mp hj) hpu henc]
      by_cases h : j=0 ∨ j+1=r <;> simp [h]
    exact hone.trans (run_endpoint_sum r hb.1)
  simp_rw [hlocal]
  let e : Fin t.length ≃ Fin (t.map (fun b => min b.1 2)).length :=
    finCongr (List.length_map _).symm
  have hs := e.sum_comp (fun p => (t.map (fun b => min b.1 2))[p.val])
  have hev : ∀ p : Fin t.length, (e p).val=p.val := fun _ => rfl
  rw [Fin.sum_univ_getElem] at hs
  simp only [hev,List.getElem_map] at hs
  exact hs

/-- Endpoint weight preserved by the existing marked-word / tuple bijection. -/
private theorem endpoint_count_wordOfTuple {n : ℕ} (i : Fin n) (t : GoodTuple n) :
    (endpoints (wordOfTuple i t.val t.property.2.2)).card = tupleEndpoints t.val := by
  rw [endpoint_count_raw _ i (rawPairs t.val)]
  · simp [tupleEndpoints, rawPairs, List.map_map, Function.comp_def]
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨t.property.2.1 c hc, by omega⟩
  · rw [linearize_wordOfTuple, tupleList_eq_rawPairs]



/- ===== EndpointDoubleCount ===== -/

open D5.S1.Words.AssociatedMersenne
open CircularWords RunTupleBijection MarkedDegreeEnumeration
open Classical
open scoped BigOperators
set_option maxHeartbeats 3000000

local notation "t" => (1 + Polynomial.X : Polynomial ℤ)

private def runWeight (n ell : ℕ) : Polynomial ℤ :=
  ∑ w : AMWord n, if runCount w.val = ell then t^(endpoints w.val).card else 0

private def tupleWeight (n ell : ℕ) : Polynomial ℤ :=
  ∑ u : RunTuples n ell, t ^ tupleEndpoints u.val.val

private instance (n : ℕ) : Fintype (MarkedWords n) := inferInstanceAs
  (Fintype {p : (Fin n → Bool) × Fin n // Admissible p.1 ∧ IsMarkedStart p.1 p.2})

private def markSigmaEquiv (n : ℕ) :
    ((w : AMWord n) × {i : Fin n // IsMarkedStart w.val i}) ≃ MarkedWords n where
  toFun p := ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
  invFun p := ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private lemma extractMarked_endpoints {n : ℕ} (p : MarkedWords n) :
    (endpoints p.val.1).card = tupleEndpoints (extractMarked p).2.val := by
  have h := endpoint_count_wordOfTuple (extractMarked p).1 (extractMarked p).2
  have he := congrArg (fun q : MarkedWords n => q.val.1) ((markedTupleEquiv n).left_inv p)
  change wordOfTuple (extractMarked p).1 (extractMarked p).2.val
    (extractMarked p).2.property.2.2 = p.val.1 at he
  rw [he] at h
  exact h

/-- Endpoint-weighted form of the existing marked-boundary double count. -/
private theorem marked_endpoint_double_count (n ell : ℕ) :
    (ell : Polynomial ℤ) * runWeight n ell = (n : Polynomial ℤ) * tupleWeight n ell := by
  have hmark : (∑ p : MarkedWords n,
      if runCount p.val.1 = ell then t^(endpoints p.val.1).card else 0) =
      (ell : Polynomial ℤ)*runWeight n ell := by
    rw [← (markSigmaEquiv n).sum_comp]
    rw [Fintype.sum_sigma]
    change (∑ w : AMWord n, ∑ i : {i : Fin n // IsMarkedStart w.val i},
      if runCount w.val=ell then t^(endpoints w.val).card else 0) = _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_marks]
    unfold runWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : runCount w.val = ell <;> simp [h]
  have htuple : (∑ p : Fin n × GoodTuple n,
      if p.2.val.length = ell then t^tupleEndpoints p.2.val else 0) =
      (n : Polynomial ℤ)*tupleWeight n ell := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    congr 1
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _ => by simp) _
  have he := (markedTupleEquiv n).sum_comp
    (fun p : Fin n × GoodTuple n => if p.2.val.length=ell then t^tupleEndpoints p.2.val else 0)
  change (∑ p : MarkedWords n,
    if (extractMarked p).2.val.length=ell then t^tupleEndpoints (extractMarked p).2.val else 0) = _ at he
  simp_rw [← extractMarked_runs, ← extractMarked_endpoints] at he
  rw [hmark,htuple] at he
  exact he

private lemma runWeight_partition (n : ℕ) :
    (cubePoly n).map (Nat.castRingHom ℤ) = ∑ ell ∈ Finset.range (n+1), runWeight n ell := by
  rw [cubePoly_endpoint_sum]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]
  unfold runWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hr := runCount_le w.val
  simp [Finset.sum_ite_eq',Finset.mem_range, Nat.lt_succ_of_le hr]

private lemma runWeight_zero (n : ℕ) : runWeight n 0 = 1 := by
  unfold runWeight
  have he : ∀ w : AMWord n, runCount w.val=0 ↔ w.val=(fun _ => false) := by
    intro w
    exact runCount_zero_iff w.val w.property
  simp_rw [he]
  rw [Finset.sum_eq_single (⟨fun _ => false,zero_admissible n⟩ : AMWord n)]
  · have hz : endpoints (fun _ : Fin n => false)=∅ := by
      ext q
      simp [endpoints,IsEndpoint]
    simp [hz]
  · intro w hw hn
    have hv : w.val ≠ (fun _ => false) := by intro h; exact hn (Subtype.ext h)
    simp [hv]
  · simp



/- ===== EndpointBlockSeries ===== -/

open D5.S1.Words.AssociatedMersenne
open CircularWords RunTupleBijection TransferTuples
open Classical
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

local notation "Z" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
local notation "T" => (PowerSeries.C t : PowerSeries (Polynomial ℤ))

/-- Endpoint-weighted circular block series. -/
private def blockSeries : PowerSeries (Polynomial ℤ) :=
  (Z^3*T + Z^5*T^2*geom (Z^2))*geom Z

private def endpointRunPartial (N : ℕ) : PowerSeries (Polynomial ℤ) :=
  ∑ a : Fin (N+2), PowerSeries.monomial (2*(a.val+1)+1) (t^min (a.val+1) 2)

private def endpointLetter (b : ℕ × ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.monomial (2*b.1+1+b.2) (t^min b.1 2)


private def endpointLetterPartial (N : ℕ) : PowerSeries (Polynomial ℤ) :=
  ∑ b : Fin (N+2) × Fin (N+2), endpointLetter (alphabetPair b)

private lemma endpointRunPartial_explicit (N : ℕ) : endpointRunPartial N =
    Z^3*T+Z^5*T^2*(∑ j : Fin (N+1), (Z^2)^j.val) := by
  rw [endpointRunPartial,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,Nat.zero_add,show min 1 2=1 from rfl,pow_one]
  rw [show (2*1+1:ℕ)=3 from rfl,PowerSeries.monomial_eq_C_mul_X_pow,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hr : min (j.val+1+1) 2=2 := by omega
    rw [hr,PowerSeries.monomial_eq_C_mul_X_pow,map_pow]
    have he : 2*(j.val+1+1)+1=5+2*j.val := by omega
    rw [he,pow_add,← pow_mul]
    ring

private lemma endpointLetterPartial_explicit (N : ℕ) : endpointLetterPartial N =
    endpointRunPartial N * (∑ j : Fin (N+2), Z^j.val) := by
  rw [endpointLetterPartial,Fintype.sum_prod_type]
  change (∑ r : Fin (N+2), ∑ s : Fin (N+2),
    PowerSeries.monomial (2*(r.val+1)+1+s.val) (t^min (r.val+1) 2)) = _
  rw [endpointRunPartial,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  simp only [PowerSeries.monomial_eq_C_mul_X_pow,pow_add]
  ring

private lemma endpointLetterPartial_approx (N : ℕ) : AgreeUpTo N blockSeries (endpointLetterPartial N) := by
  rw [endpointLetterPartial_explicit,endpointRunPartial_explicit]
  have hg2 : AgreeUpTo N (geom (Z^2)) (∑ j : Fin (N+1), (Z^2)^j.val) := by
    have he : PowerSeries.monomial 2 ((Polynomial.X : Polynomial ℤ)^0)=Z^2 := by simp [PowerSeries.X_pow_eq]
    have ha := geom_monomial_approx 2 0 N (by omega)
    rw [he] at ha
    simpa only [Fin.sum_univ_eq_sum_range] using ha
  have hg1 : AgreeUpTo N (geom Z) (∑ j : Fin (N+2), Z^j.val) := by
    have he : PowerSeries.monomial 1 ((Polynomial.X : Polynomial ℤ)^0)=Z := by simp [← PowerSeries.X_eq]
    have ha := geom_monomial_approx 1 0 (N+1) (by omega)
    rw [he] at ha
    intro m hm
    simpa only [Fin.sum_univ_eq_sum_range] using ha m (by omega)
  have hrun : AgreeUpTo N (Z^3*T + Z^5*T^2*geom (Z^2))
      (Z^3*T + Z^5*T^2*(∑ j : Fin (N+1), (Z^2)^j.val)) :=
    AgreeUpTo.add (fun _ _ => rfl)
      (AgreeUpTo.mul (fun _ _ => rfl) hg2)
  exact AgreeUpTo.mul hrun hg1

private lemma agree_pow {N : ℕ} {f g : PowerSeries (Polynomial ℤ)} (h : AgreeUpTo N f g)
    (ell : ℕ) : AgreeUpTo N (f^ell) (g^ell) := by
  induction ell with
  | zero => exact fun _ _ => rfl
  | succ ell ih =>
    simp only [pow_succ]
    exact AgreeUpTo.mul ih h

private lemma endpointLetter_prod (u : List (ℕ × ℕ)) :
    (u.map endpointLetter).prod = PowerSeries.monomial (transferLength u) (t^tupleEndpoints u) := by
  induction u with
  | nil =>
    change 1 = (PowerSeries.monomial 0) (t^0)
    simp
  | cons b u ih =>
    simp only [List.map_cons,List.prod_cons,ih,endpointLetter,
      PowerSeries.monomial_mul_monomial]
    have hlen : transferLength (b::u)=2*b.1+1+b.2+transferLength u := rfl
    rw [hlen]
    simp only [tupleEndpoints,List.map_cons,List.sum_cons,← pow_add]

private lemma blockSeries_coefficient_tuples (n ell : ℕ) :
    PowerSeries.coeff n (blockSeries^(ell+1)) =
      ∑ u : RunTuples n (ell+1), t^tupleEndpoints u.val.val := by
  rw [agree_pow (endpointLetterPartial_approx n) (ell+1) n (le_refl n)]
  rw [endpointLetterPartial,Fintype.sum_pow,map_sum]
  have hprod (f : Fin (ell+1) → Fin (n+2) × Fin (n+2)) :
      (∏ i, endpointLetter (alphabetPair (f i))) =
      PowerSeries.monomial (transferLength (boundedList n (ell+1) f))
        (t^tupleEndpoints (boundedList n (ell+1) f)) := by
    rw [← List.prod_ofFn]
    have he : List.ofFn (fun i => endpointLetter (alphabetPair (f i))) =
      (boundedList n (ell+1) f).map endpointLetter := by
        change List.ofFn (fun i => endpointLetter (alphabetPair (f i))) =
          (List.ofFn (fun i => alphabetPair (f i))).map endpointLetter
        rw [List.map_ofFn]
        rfl
    rw [he,endpointLetter_prod]
  simp_rw [hprod,PowerSeries.coeff_monomial]
  have hi (f : Fin (ell+1) → Fin (n+2) × Fin (n+2)) :
      (if n=transferLength (boundedList n (ell+1) f) then
        t^tupleEndpoints (boundedList n (ell+1) f) else 0) =
      (if transferLength (boundedList n (ell+1) f)=n then
        t^tupleEndpoints (boundedList n (ell+1) f) else 0)  := by simp only [eq_comm]
  simp_rw [hi]
  exact bounded_weight_sum n ell (fun u => t^tupleEndpoints u)

private lemma blockSeries_constant : PowerSeries.constantCoeff blockSeries = 0 := by
  simp [blockSeries]

private lemma blockSeries_pow_low (ell n : ℕ) (h : n < ell) :
    PowerSeries.coeff n (blockSeries^ell) = 0 := by
  have hd : (PowerSeries.X : PowerSeries (Polynomial ℤ)) ∣ blockSeries :=
    PowerSeries.X_dvd_iff.mpr blockSeries_constant
  exact (PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hd ell)) n h



/- ===== EndpointGeneratingFunction ===== -/

open D5.S1.Words.AssociatedMersenne
open CircularWords RunTupleBijection MarkedDegreeEnumeration TransferTuples TransferResolvent
open Classical
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

local notation "D" => (PowerSeries.derivative (Polynomial ℤ))

private lemma geom_partial_approx (N : ℕ) :
    AgreeUpTo N (geom blockSeries) (∑ ell ∈ Finset.range (N+1),blockSeries^ell) := by
  intro n hn
  rw [geom_finite_identity blockSeries N blockSeries_constant]
  rw [map_add,PowerSeries.coeff_mul]
  have hz : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff p.1 (blockSeries^(N+1))*PowerSeries.coeff p.2 (geom blockSeries))=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [blockSeries_pow_low (N+1) p.1 (by omega),zero_mul]
  rw [hz,add_zero]

private lemma coeff_marked_blocks (n : ℕ) :
    PowerSeries.coeff n (Z*D blockSeries*geom blockSeries) =
      ∑ ell ∈ Finset.range (n+1),PowerSeries.coeff n (Z*D blockSeries*blockSeries^ell) := by
  have h := AgreeUpTo.mul
    (show AgreeUpTo n (Z*D blockSeries) (Z*D blockSeries) from fun _ _ => rfl)
    (geom_partial_approx n)
  rw [h n (le_refl n),Finset.mul_sum,map_sum]

private lemma marked_block_coefficient (n ell : ℕ) :
    (ell+1 : Polynomial ℤ)*PowerSeries.coeff n (Z*D blockSeries*blockSeries^ell) =
      (n : Polynomial ℤ)*PowerSeries.coeff n (blockSeries^(ell+1)) := by
  have h := congrArg (fun f : PowerSeries (Polynomial ℤ) => PowerSeries.coeff n (Z*f))
    (PowerSeries.derivative_pow blockSeries (ell+1))
  rw [coeff_euler] at h
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  have he : (ell+1 : PowerSeries (Polynomial ℤ))=PowerSeries.C (ell+1 : Polynomial ℤ) := by simp
  rw [he] at h
  have hp : Z*(PowerSeries.C (ell+1 : Polynomial ℤ)*blockSeries^ell*D blockSeries) =
    PowerSeries.C (ell+1 : Polynomial ℤ)*(Z*D blockSeries*blockSeries^ell) := by ring
  rw [hp,PowerSeries.coeff_C_mul] at h
  exact h.symm

private lemma runWeight_marked_coeff (n ell : ℕ) :
    runWeight n (ell+1) = PowerSeries.coeff n (Z*D blockSeries*blockSeries^ell) := by
  have hc := marked_endpoint_double_count n (ell+1)
  have hb := marked_block_coefficient n ell
  rw [blockSeries_coefficient_tuples] at hb
  change (ell+1 : Polynomial ℤ)*_ = (n : Polynomial ℤ)*tupleWeight n (ell+1) at hb
  have h : (ell+1 : Polynomial ℤ)*runWeight n (ell+1) =
      (ell+1 : Polynomial ℤ)*PowerSeries.coeff n (Z*D blockSeries*blockSeries^ell) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hc.trans hb.symm
  have hne : (ell+1 : Polynomial ℤ) ≠ 0 := by exact_mod_cast (show (ell+1 : ℤ) ≠ 0 by omega)
  exact mul_left_cancel₀ hne h

private lemma runWeight_above (n ell : ℕ) (h : n < ell) : runWeight n ell = 0 := by
  unfold runWeight
  apply Finset.sum_eq_zero
  intro w hw
  have hr := runCount_le w.val
  simp [show runCount w.val ≠ ell by omega]

private lemma coeff_geom_z (n : ℕ) : PowerSeries.coeff n (geom Z) = 1 := by
  have he : PowerSeries.monomial 1 ((Polynomial.X : Polynomial ℤ)^0)=Z := by simp [← PowerSeries.X_eq]
  have ha := geom_monomial_approx 1 0 n (by omega)
  rw [he] at ha
  rw [ha n (le_refl n),map_sum]
  simp [PowerSeries.coeff_X_pow,Finset.sum_ite_eq',Finset.mem_range]

/-- The circular weighted count is the scalar marked-block resolvent. -/
private theorem cubeSeries_eq_resolvent :
    cubeSeries = Z*geom Z + Z*D blockSeries*geom blockSeries := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [cubeSeries]
  | succ n =>
    rw [map_add]
    have hgz : PowerSeries.coeff (n+1) (Z*geom Z) = 1 := by
      rw [← pow_one Z,PowerSeries.coeff_X_pow_mul]
      simpa only [pow_one] using coeff_geom_z n
    rw [hgz]
    rw [show PowerSeries.coeff (n+1) cubeSeries=(cubePoly (n+1)).map (Nat.castRingHom ℤ) by simp [cubeSeries]]
    rw [runWeight_partition,Finset.sum_range_succ',runWeight_zero]
    rw [coeff_marked_blocks]
    simp_rw [← runWeight_marked_coeff]
    rw [Finset.sum_range_succ (f := fun k => runWeight (n+1) (k+1)) (n+1),
      runWeight_above (n+1) (n+1+1) (by omega),add_zero]
    ring



/- ===== CubePolynomial ===== -/

open D5.S1.Words.AssociatedMersenne.TransferTuples
open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private def blockDen : PowerSeries (Polynomial ℤ) := (1-z)*(1-z^2)
private def blockNum : PowerSeries (Polynomial ℤ) := (1+x)*z^3+x*(1+x)*z^5

private lemma geom_z_inverse : (1-z)*geom z = 1 := by
  exact geom_mul z (by simp [z])

private lemma blockSeries_cleared : blockDen*blockSeries = blockNum := by
  have hg := geom_z_inverse
  have hg2 := geom_X2
  change (1-z^2)*geom (z^2)=1 at hg2
  have ht : (PowerSeries.C (1+Polynomial.X : Polynomial ℤ) : PowerSeries (Polynomial ℤ))=1+x := by simp [x]
  unfold blockDen blockSeries blockNum
  rw [ht]
  change (1-z)*(1-z^2)*((z^3*(1+x)+z^5*(1+x)^2*geom (z^2))*geom z)=_
  linear_combination (1-z^2)*(z^3*(1+x)+z^5*(1+x)^2*geom (z^2))*hg + z^5*(1+x)^2*hg2

private lemma amcDen_factor : amcDen = blockDen*(1-blockSeries) := by
  have h := blockSeries_cleared
  unfold amcDen blockDen blockNum at *
  linear_combination h

private lemma marked_resolvent_cleared :
    (z*D blockSeries*geom blockSeries)*amcDen = z*D blockSeries*blockDen := by
  rw [amcDen_factor]
  have hg := geom_mul blockSeries blockSeries_constant
  linear_combination z*D blockSeries*blockDen*hg

private lemma block_derivative_cleared :
    blockDen*D blockSeries = D blockNum-D blockDen*blockSeries := by
  have h := congrArg D blockSeries_cleared
  simp only [Derivation.leibniz,smul_eq_mul] at h
  linear_combination h

private lemma derivative_blockDen : D blockDen = -(1-z^2)-2*z*(1-z) := by
  simp [blockDen,z,Derivation.leibniz,smul_eq_mul,PowerSeries.derivative_pow]
  ring

private lemma derivative_blockNum : D blockNum = 3*(1+x)*z^2+5*x*(1+x)*z^4 := by
  simp [blockNum,x,z,Derivation.leibniz,smul_eq_mul,PowerSeries.derivative_pow]
  ring

/-- AMC-1, in the exact binding cleared-denominator form. -/
theorem result : claim := by
  change cubeSeries*(1-z^2)*amcDen=amcNum*(1-z^2)-2*z^2*amcDen
  have hcube := cubeSeries_eq_resolvent
  change cubeSeries=z*geom z+z*D blockSeries*geom blockSeries at hcube
  rw [hcube]
  have hf := marked_resolvent_cleared
  have hd := block_derivative_cleared
  rw [derivative_blockDen,derivative_blockNum] at hd
  have hb := blockSeries_cleared
  have hg := geom_z_inverse
  unfold blockDen blockNum amcDen amcNum at *
  linear_combination (1-z^2)*hf + z*(1-z^2)*hd +
    z*(1-z^2)^2*(1-blockSeries)*hg + (z*geom z*(1-z^2)+2*z^2)*hb

end
end D5.S3.Combinatorics.Hamming.AssociatedMersenneCubePolynomial
