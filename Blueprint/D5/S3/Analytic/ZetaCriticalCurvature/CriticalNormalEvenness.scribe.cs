using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCriticalCurvature;

internal sealed class CriticalNormalEvennessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection-even scalar potentials have zero first normal derivative at the fixed axis.",
        H("Critical Normal Evenness"),
        Blocks(
            Theorem(
                "even-has-deriv-at-zero",
                "even_hasDerivAt_zero",
                "Even Has Deriv At Zero",
                "A differentiable even real function has zero derivative at the reflection fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "deriv-even-zero",
                "deriv_even_zero",
                "Deriv Even Zero",
                "deriv formulation of the same reflection obstruction.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "critical-normal-derivative-zero",
                "critical_normal_derivative_zero",
                "Critical Normal Derivative Zero",
                "Parameterized potential version. For every fixed tangential coordinate t, normal reflection symmetry removes the first normal derivative.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "critical-normal-deriv-zero",
                "critical_normal_deriv_zero",
                "Critical Normal Deriv Zero",
                "Pointwise family formulation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
