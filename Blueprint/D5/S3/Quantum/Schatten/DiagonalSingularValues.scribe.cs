using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class DiagonalSingularValuesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/DiagonalSingularValues";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular values of nonnegative diagonal matrices.",
        H("Singular values of nonnegative diagonal matrices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-diagonalsingularvalues-singularvaluessorted-diagonal-of-antitone-perm"),
                DeclarationHandle.Create(Module + ".singularValuesSorted_diagonal_of_antitone_perm"),
                H("Sorting a diagonal spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("Let a be a nonnegative real vector and σ a permutation for which a∘σ is decreasing. Then the ith decreasing singular value of diag(a) equals aσ(i), with the canonical identification of the finite index types. Repeated entries and zero entries are included."))),
                DescribeRole.Theorem))));
}
