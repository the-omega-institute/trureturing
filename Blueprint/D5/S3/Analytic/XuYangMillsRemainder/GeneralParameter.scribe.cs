using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class GeneralParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact general-parameter Mills remainder classification target, with compiled endpoint-sign consequences.",
        H("General-parameter Mills remainder classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("f-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F"),
                H("Original signed remainder normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "F n a x is the original signed remainder (-1)^n * D n x a, "
                    + "where D is imported from the frozen Xu-Yang Mills source and retains "
                    + "the Gaussian Mills ratio, Gamma coefficients, and finite truncation.")))),
            Describe.Lean(
                DescribeId.Create("theorem-21-target"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21"),
                H("Theorem 2.1 target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every n >= 2 and real a, the positive global-sign predicate is "
                        + "equivalent to complete monotonicity and to a <= theta (n-2); "
                        + "the negative global-sign predicate is equivalent to complete "
                        + "monotonicity of -F and to a >= theta (n-1), with both endpoints "
                        + "included. The proposition is retained as the exact source target.")),
                    Paragraph(Text(
                        "The current compiled checkpoint proves the zeroth-order sign "
                        + "projection from complete monotonicity and proves the general "
                        + "one-sided endpoint-limit sign lemma. The general-a coefficient "
                        + "identity, strict adjacent weighted-moment comparison, and the "
                        + "two Mills endpoint limits remain open."))),
                DescribeRole.Definition))));
}
