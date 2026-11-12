// Copyright (c) 2026 Jeffrey Li. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Jeffrey Li
// Source: LeanPool/EilenbergZilber at 8bbde3a6de815108d41922c9362ebbe38422663a.
// Original: jeffrey-dot-li/lean-homology at 40c5aae235b0f499ebfc1e68ce574a62b531203c.
// Author release: fd0147a1ffe4f3c14c247574e148893d7cdf8cf6, LeanPool PR 588.
// Modifications: mathematical exposition, canonical identifier spellings, and typed Scribe document construction.
// Full legal custody: Library/HomologicalAlgebra/li2026bisimplicialeilenbergzilber.md.

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.EilenbergZilber;

internal sealed class ShuffleSignsDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signs of inserted shuffle steps", H("Signs of inserted shuffle steps"), Blocks(
        Paragraph(Text("All shuffle degrees are natural numbers and every sign is an integer. Inserting a first-coordinate step at j into a (p,q)-shuffle contributes t-j inversions, where t is insertLeftIndex. Thus its sign is (-1)^(t-j) times the original sign. The second-coordinate insertion is the coordinate swap of a first-coordinate insertion and acquires the corresponding Koszul factors.")),
        Paragraph(Text("The inversion sum is split at the insertion index. The noninserted terms match the old sum, while the inserted term supplies exactly the missing exponent. These identities supply the signs of the two boundary families in the shuffle chain map.")),
        Describe.Lean(DescribeId.Create("ez-shufflesigns-insertleftstep-isleftstep-at-eb751a"), DeclarationHandle.Create("D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertLeftStep_isLeftStep_at"), H("insertLeftStep_isLeftStep_at"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HomologicalAlgebra/li2026bisimplicialeilenbergzilber")), Blocks(Paragraph(Text("The inserted step is a left step: the first coordinate increases from `j` to `succAbove j (ν.1 t).1 > j` at the insertion vertex.")), Paragraph(Text("In this notation, lemma insertLeftStep_isLeftStep_at {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) (ht : (insertLeftIndex ν j).val < p + 1 + q) : isLeftStep (insertLeftStep ν j) ⟨(insertLeftIndex ν j).val, ht⟩."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("ez-shufflesigns-sign-insertleftstep-d3c314"), DeclarationHandle.Create("D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertLeftStep"), H("sign_insertLeftStep"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HomologicalAlgebra/li2026bisimplicialeilenbergzilber")), Blocks(Paragraph(Text("Sign relation for left insertion: `(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`. Derived from `invCount_insertLeftStep_add` via exponent arithmetic: the identity `invCount(μ) + j = invCount(ν) + t` gives `(-1)^(invCount(μ) + j) = (-1)^(invCount(ν) + t)`, hence `sign(μ) * (-1)^j = sign(ν) * (-1)^t`, and multiplying both sides by `(-1)^(j+t)` (using `(-1)^(2k) = 1`) yields the result.")), Paragraph(Text("In this notation, lemma sign_insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val = (-1 : ℤ) ^ j.val * ν.sign."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("ez-shufflesigns-insertrightstep-eq-swap-0ba73c"), DeclarationHandle.Create("D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.insertRightStep_eq_swap"), H("insertRightStep_eq_swap"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HomologicalAlgebra/li2026bisimplicialeilenbergzilber")), Blocks(Paragraph(Text("Right insertion is left insertion on the swapped shuffle.")), Paragraph(Text("In this notation, lemma insertRightStep_eq_swap {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : (insertRightStep ν k).swap = insertLeftStep (ν.swap) k."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("ez-shufflesigns-sign-insertrightstep-6290a8"), DeclarationHandle.Create("D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns.sign_insertRightStep"), H("sign_insertRightStep"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HomologicalAlgebra/li2026bisimplicialeilenbergzilber")), Blocks(Paragraph(Text("Sign relation for right insertion: `(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) = (-1)^p * (-1)^k * ν.sign`.")), Paragraph(Text("In this notation, lemma sign_insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val = (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign)."))), DescribeRole.Theorem))));
}
