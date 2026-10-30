using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class InverseSquareGammaConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive the full logarithmic and actual completed-zeta Gamma passage "
            + "from a common inverse-square transform envelope.",
        H("Inverse-square decay pays the full Gamma passage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gamma-inverse-square-passage"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/InverseSquareGammaConvergence."
                    + "actual_gamma_tendsto_of_uniform_inverse_square"),
                H("A genuine logarithmic form domain and actual Gamma limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let continuous complex functions V_n converge pointwise to "
                        + "a continuous U, and assume the same real D bounds "
                        + "every norm |V_n(t)| by D/(1+t^2). Then U has the complete "
                        + "(1+log(1+|t|))-weighted square domain, every error V_n-U "
                        + "has that domain, and the full weighted error integral tends "
                        + "to zero. The actual Gamma integrands of U and every V_n "
                        + "are integrable. The original completed-zeta Gamma quadratic form "
                        + "with symbol 2*pi*mu and normalization 1/(2*pi) converges.")),
                    Paragraph(Text(
                        "The pointwise envelope passes to U. A direct polynomial "
                        + "inequality bounds the weighted square by the integrable "
                        + "Cauchy density 2D^2/(1+t^2), and bounds the error by "
                        + "8D^2/(1+t^2). Dominated convergence proves the full "
                        + "logarithmic limit; the existing actual Gamma continuity "
                        + "theorem then supplies the stated consequence.")),
                    Paragraph(Text(
                        "This is an analytic domain and continuity theorem. It "
                        + "does not infer logarithmic regularity from physical H6 "
                        + "alone, remove the common envelope, identify an arbitrary "
                        + "physical source, prove a form core for all V, or assert RH."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaGamma/LogarithmicFormContinuity"))
        ]));
}
