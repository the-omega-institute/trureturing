using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence.MeanKernels;

internal sealed class BelavkinStaszewskiPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var rho = F.Id("rho");
        var sigma = F.Id("sigma");

        return DocumentDefinition.Create(ScribeNode.Create(
            "A positive-density logarithmic divergence equals its weighted affine-inverse path energy.",
            H("The Positive-Density Logarithmic Path Identity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("positive-density-logarithmic-divergence-equals-affine-inverse-path"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath.belavkin_staszewski_path"),
                    H("The logarithmic divergence is an affine-inverse path integral"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("rho"),
                        Call("PositiveDefiniteDensityMatrix"),
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("sigma"),
                            Call("PositiveDefiniteDensityMatrix"),
                            Equal(
                                Call("belavkinStaszewskiDivergence", rho, sigma),
                                Call("rightLogarithmicPathEnergy", rho, sigma))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let rho and sigma be finite square complex positive-definite matrices, "
                            + "each with trace one. Define their logarithmic divergence as the trace "
                            + "of rho times the continuous-functional-calculus logarithm of sqrt(rho) "
                            + "times inverse(sigma) times sqrt(rho). Put delta = rho - sigma and "
                            + "m(u) = (1-u) sigma + u rho. The theorem identifies that divergence "
                            + "with the integral from zero to one of (1-u) times the trace of delta "
                            + "times inverse(m(u)) times delta.")),
                        Paragraph(Text(
                            "The proof applies mathlib's exact scalar complex-logarithm integral and "
                            + "moves it through continuous functional calculus using cfc_setIntegral. "
                            + "Positive definiteness supplies every inverse and makes the sandwiched "
                            + "matrix logarithm legitimate. The frozen affine matrix inversion theorem "
                            + "then changes the inverse weighted sum into sigma times inverse(m(u)) "
                            + "times rho. Trace cyclicity, rho = m(u) + (1-u) delta, and trace(delta) "
                            + "= 0 yield the stated weight without assuming that rho and sigma commute.")),
                        Paragraph(Text(
                            "The hypotheses are satisfiable: taking rho = sigma to be any strictly "
                            + "positive trace-one diagonal matrix makes both sides zero. The theorem "
                            + "does not assume its logarithm representation or its target path identity; "
                            + "both are derived from positivity, trace normalization, library functional "
                            + "calculus, and finite-dimensional matrix algebra."))),
                    DescribeRole.Theorem))));
    }
}
