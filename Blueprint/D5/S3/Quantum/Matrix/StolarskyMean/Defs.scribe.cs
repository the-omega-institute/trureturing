using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/Defs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stolarsky mean matrices and their positive eigenvalue count.",
        H("Stolarsky means and class A"), Blocks(
            Definition("stolarsky", "The Stolarsky mean", "The mean has diagonal value a. At parameter zero it is the logarithmic mean, and at parameter one it is the identric mean. At other parameters it is the real power of the divided difference of the power function. Positivity assumptions are supplied by the theorems using this total real function."),
            Definition("stolarskyMatrix", "A finite mean matrix", "The matrix entry at i,j is the Stolarsky mean of the two members of the given real family."),
            Definition("numPosEig", "The positive eigenvalue count", "For a real Hermitian matrix, count the strictly positive eigenvalues with multiplicities. The value for a non-Hermitian matrix is zero."),
            Definition("InClassA", "Class A", "A matrix belongs to class A when all entries are strictly positive and exactly one eigenvalue is strictly positive."),
            Definition("claim", "The Stolarsky matrix assertion", "Every positive family of nonzero size gives a class A matrix at every real parameter at least two. For every parameter from zero inclusive to two exclusive, some positive finite family gives a matrix outside class A."))));

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-defs-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
