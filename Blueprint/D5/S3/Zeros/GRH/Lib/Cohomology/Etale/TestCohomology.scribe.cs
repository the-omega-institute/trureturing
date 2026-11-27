using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class TestCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Test Cohomology", H("Test Cohomology"),
        Blocks(
            Paragraph(Text("Test rings, functors of points, locally constant coefficients, cohomology as Ext.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestCohomology.baseChangeOf"),
                H("baseChangeOf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s: X → h_R and a ring map φ: R → B, the base change X_B = X ×_{h_R} h_B.")))))));
}
