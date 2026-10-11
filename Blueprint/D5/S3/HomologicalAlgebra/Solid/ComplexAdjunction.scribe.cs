using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ComplexAdjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Complex Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-complexadjunction-exactderivedhomologyiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.exactDerivedHomologyIso"),
                H("exact Derived Homology Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact derived functors commute with homology in every integer degree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-complexadjunction-derivedinclusion-postcomp-isrightderivedfunctor"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.derivedInclusion_postcomp_isRightDerivedFunctor"),
                H("derived Inclusion postcomp is Right Derived Functor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact derived inclusion remains a right-derived functor after any postcomposition. This discharges the right-derived composite obligation in `Adjunction.derived`; it requires no existence or adjunction assumption for derived solidification."))),
                DescribeRole.Theorem))));
}
