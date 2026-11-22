using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class DimFourDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bounds in dimension four",
        H("The refined BMV lower bounds in dimension four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-dim-four-cube-root"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/DimFour.cubeRoot_bound"),
                H("The cube-root trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices X and B of size four, the mean with p copies of X cubed and three copies of B dominates the trace of the cube of X to the power p times B. The comparison holds for p equal to five, six, or seven and uses all four spectral coordinates of X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-dim-four-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/DimFour.product_bound"),
                H("The spectral-power trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices A and B of size four, take X to be the positive semidefinite cube root of A. The word mean dominates the trace of the cube of the product of the spectral power A to the exponent p/3 and B. The spectral power is defined also at zero eigenvalues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-dim-four-exponential"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/DimFour.exponential_bound"),
                H("The exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every complex Hermitian pair of size four, apply the cube-root comparison to the exponential of H/3 and the exponential of K. The exact dyadic trace-power comparison bounds the trace of the exponential of p H plus 3 K by this word mean."))),
                DescribeRole.Theorem))));
}
