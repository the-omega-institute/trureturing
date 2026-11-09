using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class AveragingRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local interval integrability.",
        H("Regularity of forward averages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("locally-bounded-measurable-interval-integrable"),
                DeclarationHandle.Create(Prefix + "locallyBoundedMeasurable_intervalIntegrable"),
                H("Local interval integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A measurable real function bounded on each compact interval is integrable on every finite oriented interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-average-continuous"),
                DeclarationHandle.Create(Prefix + "windowAverage_continuous"),
                H("Continuity of window averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For R>0, the forward window average of a locally bounded measurable real function is continuous. Expressing it as the difference of values of its continuous integral primitive proves this without differentiability of the original function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-average-continuous-of-interval-integrable"),
                DeclarationHandle.Create(Prefix + "windowAverage_continuous_of_intervalIntegrable"),
                H("Continuity from interval integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a real function is interval integrable on every finite interval, each of its forward window averages is continuous. The proof writes the average as a difference of values of the continuous integral primitive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("double-average-has-deriv-at"),
                DeclarationHandle.Create(Prefix + "doubleAverage_hasDerivAt"),
                H("Derivative of a double average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For R>0, the double forward average of E has derivative at every x equal to the window average of E(y+R)-E(y), evaluated at x and divided by R. The fundamental theorem of calculus applies to the continuous first average."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("double-average-cont-diff"),
                DeclarationHandle.Create(Prefix + "doubleAverage_contDiff"),
                H("Continuous differentiability of double averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For R>0, a double forward average of a locally bounded measurable real function is continuously differentiable. Its derivative is the difference of two translates of the continuous first average, divided by R."))),
                DescribeRole.Theorem))));
}
