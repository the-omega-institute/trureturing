using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVDimThreeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bounds in dimension three",
        H("The refined BMV lower bounds in dimension three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-dim-three-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVDimThree.product_bound"),
                H("The trace-power comparison for five, six, or seven first factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices of size three, the trace of the cube of the product using the first factor's spectral power p/3 is bounded by the mean of all words with p first factors and three second factors. The ordered eigenvalue certificate and the single triangle pairing cover repeated and zero eigenvalues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-dim-three-exponential"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVDimThree.exponential_bound"),
                H("The exponential comparison for five, six, or seven first factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every complex Hermitian pair of size three, the cube-root comparison uses the exponential of one third of the first matrix and the exponential of the second matrix. The cube of the first exponential is the first factor of the words. The dyadic trace-power comparison gives the lower bound for p equal to five, six, or seven. Hägele names the five-and-three question in Section 7 of arXiv:2611.00129v1."))),
                DescribeRole.Theorem))));
}
