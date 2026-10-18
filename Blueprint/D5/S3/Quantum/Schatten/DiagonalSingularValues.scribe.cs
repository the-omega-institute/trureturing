using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class DiagonalSingularValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular values of nonnegative diagonal matrices.", H("DiagonalSingularValues"), Blocks(
            Paragraph(Text("The Gram matrix of a nonnegative real diagonal matrix is the diagonal of the squared entries. Its eigenvalues are a permutation of those squared entries. Taking nonnegative square roots recovers the original entries, and any permutation sorting them in decreasing order therefore gives exactly the sorted singular values. Repeated entries and zero entries are included.")))));
}
