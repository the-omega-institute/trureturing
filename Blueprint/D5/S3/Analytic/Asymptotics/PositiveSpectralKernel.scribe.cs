using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PositiveSpectralKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Probability measures realizing products of exponential moments",
        H("Probability measures realizing products of exponential moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-probability-has-prod-exp-moment"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/PositiveSpectralKernel.exists_probability_hasProd_expMoment"),
            H("Exponential moments of a sum of bounded independent coordinates"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Probability measures carried by intervals [0,a_j] with summable lengths jointly "
                + "determine a probability measure on the sum interval. Its complex exponential moments "
                + "at every argument are the products of the moments of the factors. The construction "
                + "integrates the uniformly convergent sum of the independent coordinates."))),
            DescribeRole.Theorem))));
}
