using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class BinaryTraceZeroSimilarityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026heawoodsimilarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero trace-zero binary matrix of size three is similar to one of six explicit matrices.",
        H("Similarity of trace-zero binary matrices of size three"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-trace-zero-representatives"),
                DeclarationHandle.Create(Prefix + "representative"), H("The six representatives"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Write Eij for a matrix unit with one-based indices. The representatives in order are "
                    + "E12, E12+E23, diag(1,1,0), diag(1,1,0)+E12, E13+E21+E32, and E13+E21+E32+E23."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("binary-trace-zero-similarity"),
                DeclarationHandle.Create(Prefix + "exists_conjugate"), H("Conjugacy to a chosen representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("A nonzero binary matrix of size three and trace zero has characteristic "
                        + "polynomial X cubed plus a times X plus c. The two coefficients are binary. "
                        + "For c equal to zero, the nilpotent or repeated-root theorem supplies an ordered "
                        + "normal basis. For c equal to one, a cyclic basis gives the companion matrix.")),
                    Paragraph(Text("The change-of-basis matrix is invertible and conjugates the chosen "
                        + "representative to the input matrix.")),
                    Paragraph(Text("The matrices match the switching invariants of the six signings in the "
                        + "Heawood double cover classification."))),
                DescribeRole.Theorem))));
}
