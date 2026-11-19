using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class StrictConcaveSymmetricSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict concavity compares symmetric pairs with a common center.",
        H("Symmetric sums and strict concavity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-concave-symmetric-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum."
                    + "strictConcave_symmetric_sum"),
                H("Symmetric sums of a strictly concave function"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a strictly concave real function h on (0,infinity), and real r,s,t "
                    + "with 0<=s<t<r, one has h(r-t)+h(r+t)<h(r-s)+h(r+s). "
                    + "Both inner points are strict convex combinations of the outer pair. "
                    + "This comparison also gives strict decrease of equal-length increments."))),
                DescribeRole.Theorem))));
}
