/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/HermitianMat
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/ForMathlib/HermitianMat.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Basic
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.CFC
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.LogExp
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Reindex
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Sqrt
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Trace
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary
