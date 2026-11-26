using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class StandardLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Standard Level", H("Standard Level"),
        Blocks(
            Paragraph(Text("Finite place carries a level and gauges for the tower method; masses of K.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/StandardLevel.le_stackMeasure_boxSet"),
                H("le_stackMeasure_boxSet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a standard level at a finite place with integers R and l + i = ϱ, the measure Level.stackMeasure l (i+2) of U(V_l) gives the group K of integral isometries mass at least vol(R^×)^(i+1).")))))));
}
