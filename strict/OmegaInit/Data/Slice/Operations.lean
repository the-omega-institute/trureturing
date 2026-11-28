/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Data.Slice.Basic

port_native_records Std.Slice.SliceSize
port_definition Std.Slice.SliceSize.noConfusionType
port_definition Std.Slice.SliceSize.noConfusion
port_definition Std.Slice.SliceSize.mk.noConfusion
port_definition Std.Slice.SliceSize.ctorIdx with_native_code
port_definition Std.Slice.size with_native_code

/- Open: the unique field of Std.Slice.LawfulSliceSize compares size with
Std.Iter.length at Std.IteratorLoop.defaultImplementation for every slice. Its
parameters supply an iterator and omit a termination proof. LawfulSliceSize.mk,
.lawful, .rec, .recOn, and .casesOn all mention that field in their pinned
types. The private .mk._flat_ctor also requires the original record.
For finite iterators, lawfulSliceSizeIffFiniteLength identifies the original
field with the length of (ToIterator.iter s).ensureTermination.toList. The
length observation for arbitrary iterators, agreeing on every finite slice,
is equivalent to deciding existence of a signal in every Boolean stream
(streamDecisionIffSliceLength).

Std.Slice.toList, .toArray and .toListRev also accept arbitrary iterators.
A total implementation of any one of these three that agrees on every finite
slice decides whether an arbitrary Boolean stream ever returns true, as shown
in OmegaChecks.InitBoundaries.Collector. In the adaptive query model, a terminating
run on an all-false stream would return the same length on an iterator that
stops strictly later. noTerminatingThresholdCounter proves the obstruction and
noTerminatingCollectorOnZero checks the lengths against the official collector. -/
