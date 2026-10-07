using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class OriginalDerivedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. Exact original derived-constructor declarations of LeanEval `derived_solidification_free_CW_homology`, using the genuine unbounded D(Solid) realization and accepted exact Kan proof. No derived-existence, resolution, full-faithfulness or adjunction hypothesis is introduced. The original ordinary declarations are imported unchanged from CWSolid.Early. Challenge attribution: dagurtomas/LeanCondensed at 339ecc99fdc4bdb68ef248c16da0148dce61a639 (Apache-2.0).",
        H("Original Derived"),
        Blocks(
            Paragraph(Text("Derived solidification is constructed on arbitrary unbounded cochain complexes. "
                + "The literal derived inclusion has a left adjoint, whose ordinary-unit-induced comparison "
                + "satisfies the total-left-derived and right-Kan-extension universal properties for all "
                + "quasi-isomorphisms. The realization uses a projective generator, augmented resolutions "
                + "and both unbounded truncation telescopes.")),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-derivedsolidification"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification"),
                H("derived Solidification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("**Hole 4.** The derived solidification functor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-derivedsolidificationcounit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationCounit"),
                H("derived Solidification Counit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("**Hole 5.** The comparison map from derived solidification to degreewise solidification."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-derivedsolidification-isleftderivedfunctor"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isLeftDerivedFunctor"),
                H("derived Solidification is Left Derived Functor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("**Hole 6.** Derived solidification, together with the comparison map of the previous hole, is the total left derived functor of degreewise solidification followed by localization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-derivedsolidificationadjunction"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationAdjunction"),
                H("derived Solidification Adjunction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("**Hole 7.** The derived solidification adjunction: derived solidification is left adjoint to the derived inclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-solidification-hasleftderivedfunctor"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.solidification_hasLeftDerivedFunctor"),
                H("solidification has Left Derived Functor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual existence for all quasi-isomorphisms of arbitrary unbounded complexes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-originalderived-derivedsolidification-isrightkanextension"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isRightKanExtension"),
                H("derived Solidification is Right Kan Extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original counit has the literal right-Kan-extension universal property."))),
                DescribeRole.Theorem))));
}
