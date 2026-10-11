using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ExactDerivedHomologyNaturalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Exact Derived Homology Natural"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-exactderivedhomologynatural-exactderivedhomologynatiso-hom-app-q"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactDerivedHomologyNatural.exactDerivedHomologyNatIso_hom_app_Q"),
                H("exact Derived Homology Nat Iso hom app Q"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem))));
}
