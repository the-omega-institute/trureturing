using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class MatchingPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/MatchingPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assemble the monomial-fiber counts into formula (star).",
        H("Matching Polynomial Formula"),
        Blocks(
            Paragraph(Text(
                "All contributing exponent vectors have total degree 2k and entries at most "
                + "two. Each is a disjoint square/linear fiber. The two coefficient formulas "
                + "and the alternating factorial sum therefore determine the entire polynomial.")),
            Describe.Lean(
                DescribeId.Create("matching-esymm-product"),
                DeclarationHandle.Create(Prefix + "matchingSum_esymm_mul"),
                H("Denominator Product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplying the matching sum by (n-2k)! times (n-k)! gives the "
                    + "explicit signed elementary-symmetric numerator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-esymm-formula"),
                DeclarationHandle.Create(Prefix + "matchingSum_esymm"),
                H("Formula (star)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factorial denominator is nonzero in Q, giving the scalar-quotient "
                    + "form for every n and k with 2k at most n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-identity"),
                DeclarationHandle.Create(Prefix + "matching_identity"),
                H("Matching Identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluation in R, Mathlib Vieta, and the symmetrization coefficient "
                    + "formula prove the complete MatchingIdentity for every admissible n and k."))),
                DescribeRole.Theorem))));
}
