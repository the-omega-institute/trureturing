using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrable profiles admit measurable and square-integrable variable-length averages.",
        H("Regularity of variable-length profile averages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-average-variable-measurable"),
                DeclarationHandle.Create(Prefix + "profileAverage_variable_measurable"),
                H("Measurability for variable lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally bounded measurable E, an integrable Borel profile g, and a measurable real length H, the function sending x to the profile average at length H(x) and starting point x is measurable. The unit-interval formula expresses its numerator as a parameter integral of a jointly measurable function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-average-variable-mem-lp"),
                DeclarationHandle.Create(Prefix + "profileAverage_variable_memLp"),
                H("Square integrability for bounded positive lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite ordered interval [a,b], suppose the measurable length H lies between fixed l>0 and L. For any integrable Borel profile g, its variable-length average belongs to L squared. A compact bound B for E on [a,b+L] bounds the absolute average by 2B times the L1 norm of g divided by l."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("step-integrable"),
                DeclarationHandle.Create(Prefix + "step_integrable"),
                H("Integrability in the step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each starting point x, increments of a locally bounded measurable E are integrable as functions of their step on every finite oriented interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("step-sq-integrable"),
                DeclarationHandle.Create(Prefix + "step_sq_integrable"),
                H("Square integrability in the step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each starting point x, the square of the increment of a locally bounded measurable E is integrable as a function of its step on every finite oriented interval."))),
                DescribeRole.Theorem))));
}
