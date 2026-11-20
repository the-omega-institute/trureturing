using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class FiniteProductTruncationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact degree criterion for truncating a weighted product expansion.",
        H("Degree cutoffs for finite weighted products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-product-truncation"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Probability/FiniteProductTruncation.weighted_product_truncation"),
                H("Exactness of degree truncation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Give each assignment a strictly positive weight and each factor a nonnegative " +
                    "excess, which may depend on the assignment. Expand the product of one plus " +
                    "each excess into subset products. The weighted sum through a fixed degree " +
                    "lower bounds the weighted sum of the full products. Equality holds exactly when " +
                    "the number of positive excesses at each assignment is at most the chosen " +
                    "degree. If there are more positive excesses, their support contributes a " +
                    "strictly positive term above the cutoff. Otherwise every higher-degree term " +
                    "contains a zero factor. The weights need only be positive, so their sum can " +
                    "be any positive value when the assignment set is nonempty."))),
                DescribeRole.Theorem))));
}
