using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVThreeSpectrumCertificateDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bounds for three spectral values in every degree",
        H("The refined BMV lower bounds for three spectral values in every degree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectrum-all-degree-product"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_product"),
                H("The product lower bound in every positive degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite matrices A and B in any finite dimension, the normalized word " +
                    "trace with p copies of A and three of B bounds the trace of the cube of " +
                    "A raised to p/3 times B from below. The degree p is any positive integer and A has " +
                    "at most three distinct eigenvalues, with arbitrary multiplicities. " +
                    "The scalar discriminant in two logarithmic gaps is a finite exponential sum. " +
                    "The kernel checks its sparse integer coefficient table and the signs of all mixed " +
                    "initial values as polynomials in p minus one. A sequence of first-order equations " +
                    "propagates these signs to the entire nonnegative quadrant. The centered trace pairing " +
                    "then gives the matrix bound, with continuity covering zero roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectrum-all-degree-exponential"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_exponential"),
                H("The exponential lower bound in every positive degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian matrices H and K, the normalized word trace of their exponentials " +
                    "bounds the trace of the exponential of pH plus 3K from below. The degree p is " +
                    "any positive integer and H has at most three distinct eigenvalues. " +
                    "Hägele's dyadic trace comparison takes the product bound to this limit."))),
                DescribeRole.Theorem))));
}
