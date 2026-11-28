/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Control.MonadAttach
public import OmegaInit.Data.Option.Basic

port_definition Std.IterM.step_filterMap.match_1 with_native_code
port_definition Std.IterM.step_filterMapM.match_1 with_native_code
port_definition Std.IterM.step_filterM.match_1 with_native_code
port_definition Std.IterM.forIn_filterMapWithPostcondition.match_1 with_native_code
port_definition Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition.match_1 with_native_code

/- The official public types refer to the unrestricted Std.IterM.toArray.
The premise supplies a finite iterator. The stated interaction with the
combinator still needs a proof at a type accepted by both public kernels.
Std.IterM.toArray_filter
Std.IterM.toArray_filterMap
Std.IterM.toArray_filterMapM
Std.IterM.toArray_filterMapM_filterMapM
Std.IterM.toArray_filterMapM_filterMapWithPostcondition
Std.IterM.toArray_filterMapM_map
Std.IterM.toArray_filterMapM_mapM
Std.IterM.toArray_filterMapWithPostcondition
Std.IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition
Std.IterM.toArray_map
Std.IterM.toArray_mapM
Std.IterM.toArray_mapM_eq_toArray_filterMapM
Std.IterM.toArray_mapM_filterMapM
Std.IterM.toArray_mapM_map
Std.IterM.toArray_mapM_mapM
Std.IterM.toArray_mapWithPostcondition
Std.IterM.toArray_mapWithPostcondition_mapWithPostcondition
Std.IterM.toArray_map_eq_toArray_filterMapM
Std.IterM.toArray_map_eq_toArray_mapM
Std.IterM.toArray_map_mapM
-/

/- The official public types refer to the unrestricted Std.IterM.toList.
The premise supplies a finite iterator. The stated interaction with the
combinator still needs a proof at a type accepted by both public kernels.
Std.IterM.toList_filter
Std.IterM.toList_filterMap
Std.IterM.toList_filterMapM
Std.IterM.toList_filterMapM_filterMapM
Std.IterM.toList_filterMapM_filterMapWithPostcondition
Std.IterM.toList_filterMapM_map
Std.IterM.toList_filterMapM_mapM
Std.IterM.toList_filterMapWithPostcondition
Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition
Std.IterM.toList_map
Std.IterM.toList_mapM
Std.IterM.toList_mapM_eq_toList_filterMapM
Std.IterM.toList_mapM_filterMapM
Std.IterM.toList_mapM_map
Std.IterM.toList_mapM_mapM
Std.IterM.toList_mapWithPostcondition
Std.IterM.toList_mapWithPostcondition_mapWithPostcondition
Std.IterM.toList_map_eq_toList_filterMapM
Std.IterM.toList_map_eq_toList_mapM
Std.IterM.toList_map_mapM
Std.IterM.InternalConsumers.toList_filterMap
-/

/- The official public types refer to the unrestricted Std.IterM.toList and
Std.IterM.toListRev.
The premise supplies a finite iterator. The stated interaction with the
combinator still needs a proof at a type accepted by both public kernels.
Std.IterM.toListRev_filterMapM
Std.IterM.toListRev_filterMapWithPostcondition
Std.IterM.toListRev_mapM
Std.IterM.toListRev_mapWithPostcondition
-/

/- The official public types refer to the unrestricted Std.IterM.toListRev.
The premise supplies a finite iterator. The stated interaction with the
combinator still needs a proof at a type accepted by both public kernels.
Std.IterM.toListRev_filter
Std.IterM.toListRev_filterMap
Std.IterM.toListRev_filterMapM_filterMapM
Std.IterM.toListRev_filterMapM_filterMapWithPostcondition
Std.IterM.toListRev_filterMapM_map
Std.IterM.toListRev_filterMapM_mapM
Std.IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition
Std.IterM.toListRev_map
Std.IterM.toListRev_mapM_eq_toListRev_filterMapM
Std.IterM.toListRev_mapM_filterMapM
Std.IterM.toListRev_mapM_map
Std.IterM.toListRev_mapM_mapM
Std.IterM.toListRev_mapWithPostcondition_mapWithPostcondition
Std.IterM.toListRev_map_eq_toListRev_filterMapM
Std.IterM.toListRev_map_eq_toListRev_mapM
Std.IterM.toListRev_map_mapM
-/

/- The official public types refer to Std.Iterators.Types.FilterMap.instIteratorLoop.
The default loop used here must also run on potentially infinite iterators.
Collector.limitedOmniscienceFromFilterMapLoop gives limited omniscience from its specified
finite-input behavior. A public original-type reformulation for these finite
consumers remains open.
Std.IterM.allM_filter
Std.IterM.allM_filterMap
Std.IterM.all_filterMap
Std.IterM.anyM_filter
Std.IterM.anyM_filterMap
Std.IterM.any_filterMap
Std.IterM.foldM_filter
Std.IterM.foldM_filterM
Std.IterM.foldM_filterMap
Std.IterM.foldM_filterMapM
Std.IterM.foldM_filterMapWithPostcondition
Std.IterM.foldM_filterWithPostcondition
Std.IterM.fold_filter
Std.IterM.fold_filterM
Std.IterM.fold_filterMap
Std.IterM.fold_filterMapM
Std.IterM.fold_filterMapWithPostcondition
Std.IterM.fold_filterWithPostcondition
Std.IterM.forIn_filter
Std.IterM.forIn_filterM
Std.IterM.forIn_filterMap
Std.IterM.forIn_filterMapM
Std.IterM.forIn_filterMapWithPostcondition
Std.IterM.forIn_filterWithPostcondition
-/

/- The official public types refer to Std.Iterators.Types.FilterMap.instIteratorLoop and
Std.Iterators.Types.Map.instIteratorLoop.
The default loop used here must also run on potentially infinite iterators.
Collector.limitedOmniscienceFromFilterMapLoop and
Collector.limitedOmniscienceFromMapLoop give limited omniscience from its specified
finite-input behavior. A public original-type reformulation for these finite
consumers remains open.
Std.IterM.allM_filterM
Std.IterM.allM_filterMapM
Std.IterM.all_filterM
Std.IterM.all_filterMapM
Std.IterM.anyM_filterM
Std.IterM.anyM_filterMapM
Std.IterM.any_filterM
Std.IterM.any_filterMapM
-/

/- The official public types refer to Std.Iterators.Types.Map.instIteratorLoop.
The default loop used here must also run on potentially infinite iterators.
Collector.limitedOmniscienceFromMapLoop gives limited omniscience from its specified
finite-input behavior. A public original-type reformulation for these finite
consumers remains open.
Std.IterM.allM_map
Std.IterM.allM_mapM
Std.IterM.all_map
Std.IterM.all_mapM
Std.IterM.anyM_map
Std.IterM.anyM_mapM
Std.IterM.any_map
Std.IterM.any_mapM
Std.IterM.count_map
Std.IterM.foldM_map
Std.IterM.foldM_mapM
Std.IterM.foldM_mapWithPostcondition
Std.IterM.fold_map
Std.IterM.fold_mapM
Std.IterM.fold_mapWithPostcondition
Std.IterM.forIn_map
Std.IterM.forIn_mapM
Std.IterM.forIn_mapWithPostcondition
Std.IterM.length_map
-/

/- The original statement implies function extensionality at the universes of the
specialization in OmegaChecks.InitBoundaries.IteratorStepLift.funextOfFilter.
Std.IterM.step_filterWithPostcondition
-/

/- The original statement implies function extensionality at the universes of the
specialization in OmegaChecks.InitBoundaries.IteratorStepLift.funextOfFilterM.
Std.IterM.step_filterM
-/

/- The original statement implies function extensionality at the universes of the
specialization in OmegaChecks.InitBoundaries.IteratorStepLift.funextOfMap.
Std.IterM.step_mapWithPostcondition
-/

/- The original statement implies function extensionality at the universes of the
specialization in OmegaChecks.InitBoundaries.IteratorStepLift.funextOfMapM.
Std.IterM.step_mapM
-/

/- These original public types form in the strict kernel. The pinned proofs use
bind_congr on continuations over the inner iterator step. A proof for these
three particular continuations in the zero-axiom kernel remains open.
Std.IterM.step_filter
Std.IterM.step_filterMap
Std.IterM.step_map
-/
