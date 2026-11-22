using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatSaddleDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflecting heat saddle determines the density of the equal-mass bins and the multiplier's imaginary potential.",
        H("Reflecting heat saddle density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-gramian-saddle-radius"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.existsUnique_saddle_radius"),
                H("Unique positive saddle radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The angular average of the reciprocal saddle radius is continuous and strictly decreasing on the positive half-line. The polynomial bounds at small and large radii bracket half the window parameter, so the intermediate value theorem gives the unique radius used by the physical estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-saddle-imaginary-potential"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.imaginaryPotential_eval_at_saddle"),
                H("Evaluation of the imaginary potential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiating the potential yields an integral against the saddle density. Evaluating the radial integral and exchanging it with the angular average gives the weighted resolvent. The evaluated expression and the potential have this same derivative and both vanish at zero."))),
                DescribeRole.Theorem))));
}
