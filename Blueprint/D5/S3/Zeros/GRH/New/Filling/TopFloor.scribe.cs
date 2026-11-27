using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class TopFloorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Top Floor", H("Top Floor"),
        Blocks(
            Paragraph(Text("Finite Bessel function; shell, frequency and bottom-value bounds for its forms. Top kernel of finite system: local constancy, positivity, packet energy bound, transform.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/TopFloor.continuous_topKernel"),
                H("continuous_topKernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a standard level, an intermediate group Z and an open additive subgroup L of A, the kernel Level.topKernel L Z is jointly continuous in the two sequences of units.")))))));
}
