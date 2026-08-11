using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class LogDerivTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var index = F.Id("iota");
        var matrix = Call("Matrix", index, index, F.Id("C"));
        var m = F.Id("m");
        var x = F.Id("X");

        return DocumentDefinition.Create(ScribeNode.Create(
            "The trace identity for the integral logarithmic directional derivative.",
            H("Logarithmic Derivative Trace Identity"),
            Blocks(
                                Describe.Lean(
                    DescribeId.Create("integral-logarithmic-directional-derivative"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/LogDerivTrace.logDeriv"),
                    H("Integral logarithmic directional derivative"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.Id("logDeriv"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a complex square matrix m and direction X, logDeriv m X is " +
                            "the matrix-valued Bochner integral over positive real t of " +
                            "(m + t I)^(-1) X (m + t I)^(-1). The notation D ln in the source " +
                            "paper denotes this integral. This formal statement does not claim " +
                            "that logDeriv is the Frechet derivative of mathlib's Matrix.log; " +
                            "that identification remains outside the available mathlib API " +
                            "tracked by issue #924."))),
                    DescribeRole.Definition),
                                Describe.Lean(
                    DescribeId.Create("positive-definite-log-derivative-has-direction-trace"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv"),
                    H("Positive definite logarithmic derivative has the direction trace"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("m"),
                        Call("PositiveDefinite", matrix),
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("X"),
                            Call("Hermitian", matrix),
                            Equal(
                                Call("trace", Call("multiply", m, Call("logDeriv", m, x))),
                                Call("trace", x))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let m be positive definite and X Hermitian. Unitary spectral " +
                            "decomposition writes each resolvent in the eigenbasis of m. " +
                            "Entrywise inverse-square majorants prove Bochner integrability, " +
                            "and fixed matrix multiplication and trace commute with the " +
                            "integral by finite-dimensional continuity. Trace cyclicity reduces " +
                            "the integrand to a finite sum whose ith scalar kernel is " +
                            "lambda_i/(lambda_i+t)^2. Every lambda_i is positive and the " +
                            "integral of this kernel over positive t is one, leaving the trace " +
                            "of the unitary conjugate of X, hence the trace of X. The Hermitian " +
                            "hypothesis is retained to state the identity on the paper's " +
                            "declared domain."))),
                    DescribeRole.Theorem))));
    }

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    private static LeanDeclarationRef LeanTheorem(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Theorem,
            requireNoSorry: true);
}
