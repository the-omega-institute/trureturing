using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class WeightedFilterTailTransmutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted probability average as an exact Laplace integral",
        H("The weighted probability average as an exact Laplace integral"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-compact-probability-weighted-tail-average-eq-laplace"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/WeightedFilterTailTransmutation.exists_compact_probability_weighted_tail_average_eq_laplace"),
            H("The weighted probability average as an exact Laplace integral"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The exact Laplace integrand is the value of the averaged unweighted primitive minus its Laplace transform multiplied by the transform parameter. This identity follows from absolute integration on the forward triangle."))),
            DescribeRole.Theorem))));
}
