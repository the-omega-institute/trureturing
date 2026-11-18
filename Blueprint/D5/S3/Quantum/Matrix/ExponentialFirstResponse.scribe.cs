using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ExponentialFirstResponseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/ExponentialFirstResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first response of measurable evolution gives the operator-norm derivative "
        + "of the exponential on finite complex matrices.",
        H("Matrix exponential first response"),
        Blocks(
            Entry("derivative-operator", "derivative", "Bochner derivative operator",
                "The derivative operator at A is the interval integral of the complex "
                + "continuous linear maps that multiply H on the left by exp((1−u)A) "
                + "and on the right by exp(uA). The matrix norm is the L2 operator norm.",
                DescribeRole.Definition),
            Entry("derivative-apply", "derivative_apply", "Derivative applied to a perturbation",
                "Evaluation on an arbitrary complex matrix H commutes with the interval "
                + "integral. The resulting matrix integral is the one used in the "
                + "faithful logarithmic-mean identification.",
                DescribeRole.Theorem),
            Entry("exponential-derivative", "hasFDerivAt_exp", "Fréchet derivative at every matrix",
                "The exponential has the full complex Fréchet derivative given by this "
                + "operator at every A. For the identity contraction and a constant "
                + "generator, the exponential orbit solves the native mild equation. "
                + "Continuous residual uniqueness identifies it with the measurable "
                + "evolution. The original first-response remainder bounds the defect "
                + "on every Euclidean vector with the same coefficient. Taking the "
                + "operator norm gives a quadratic bound in the perturbation.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
