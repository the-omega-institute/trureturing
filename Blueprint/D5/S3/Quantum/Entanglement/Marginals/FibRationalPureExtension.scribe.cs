using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibRationalPureExtensionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension.rational_pure_extension_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational norm criterion for pure Fibonacci marginal extensions on two words.",
        H("Rational pure extensions on two Fibonacci words"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-rational-pure-extension"),
                DeclarationHandle.Create(Result), H("The rational norm criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let b be rational and prescribe both edge marginals to be diagonal with "
                    + "entries 0, b, and 1 minus b in the order vacuum, occupied middle, "
                    + "occupied endpoint. A trace-one pure extension with rational real and "
                    + "imaginary parts in every density matrix entry exists exactly when "
                    + "b(1 − b) is a sum of two rational squares.")),
                    Paragraph(Text(
                    "The zero vacuum entries force the pure state to be supported on "
                    + "010 and 101. Their weights are b and 1 minus b, and their coupling z "
                    + "satisfies |z|² = b(1 − b). Conversely, for b positive, let the two "
                    + "amplitudes be the positive square root of b and the conjugate of z "
                    + "divided by that root. The resulting matrix has the prescribed diagonal "
                    + "and entries z and its conjugate off the diagonal. For b zero, the "
                    + "state occupies only 101.")),
                    Paragraph(Text(
                    "At b equal to one quarter, taking z equal to the positive square root "
                    + "of three divided by four gives a pure extension. Rational real and "
                    + "imaginary parts would express three as a sum of two rational squares. "
                    + "Clearing denominators gives a sum of two integer squares with odd "
                    + "three-adic valuation, which is impossible. The diagonal mixture of "
                    + "the two words gives a rational mixed extension."))),
                DescribeRole.Theorem))));
}
