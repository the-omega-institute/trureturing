using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVUniformCornerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar corner inequality for the refined BMV lower bound",
        H("The scalar corner inequality for the refined BMV lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-uniform-corner"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner"),
                H("The centered residual is nonnegative for every positive exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For three nonnegative cube roots a, x and y and any positive number of first factors, the mixed defect " +
                    "is at least the geometric mean of the repeated-root defects at (a,a,y) and (x,x,y). The triangular " +
                    "coefficient matrix of the complete homogeneous polynomial has nonpositive two-by-two minors. " +
                    "Cauchy–Binet gives the corresponding reverse Cauchy–Schwarz comparison after compression to the " +
                    "two root vectors. Ordinary Cauchy–Schwarz then transfers the comparison through subtraction of " +
                    "the geometric term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-uniform-corner-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVUniformCorner.defect_corner_strict"),
                H("The centered residual is positive for distinct roots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The minor using the zero and highest degrees gives a strictly negative contribution to the " +
                    "compressed determinant whenever a and x differ. This makes the corner inequality strict, " +
                    "including when a root is zero."))),
                DescribeRole.Theorem))));
}
