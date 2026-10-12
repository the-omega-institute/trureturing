using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence.MeanKernels;

internal sealed class BelavkinStaszewskiPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var rho = F.Id("rho");
        var sigma = F.Id("sigma");
        var n = F.Id("n");
        var a = F.Id("A");

        return DocumentDefinition.Create(ScribeNode.Create(
            "A positive-density logarithmic divergence equals its weighted affine-inverse path energy.",
            H("The Positive-Density Logarithmic Path Identity"),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary finite index type n with decidable equality, put "
                    + "logPath(A,u) = (A-I) inverse((1-u)I+uA) for a square complex matrix A. "
                    + "The inverse is the matrix nonsingular inverse. The following two "
                    + "statements require positive definiteness, without trace normalization "
                    + "or a nonempty-index assumption.")),
                Describe.Lean(
                    DescribeId.Create("positive-matrix-log-path-interval-integrability"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath.matrixLogPath_intervalIntegrable"),
                    H("The positive-matrix logarithm path is interval integrable"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteType")), Bound("A", Call("ComplexSquareMatrix", n))],
                        Implies(Call("PosDef", a),
                            Call("IntervalIntegrable", Call("logPath", a), Call("Lebesgue"), D(0), D(1)))))),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/bhatia1997matrixanalysis")),
                    Blocks(Paragraph(Text(
                        "The scalar logarithm kernel is integrable on the compact parameter "
                        + "interval after continuous functional calculus. Its inverse expression "
                        + "equals logPath pointwise on that interval, which transfers integrability."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("positive-matrix-logarithm-path-representation"),
                    DeclarationHandle.Create(
                        "D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath.matrix_log_eq_integral_path"),
                    H("The actual matrix logarithm equals its affine-path integral"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteType")), Bound("A", Call("ComplexSquareMatrix", n))],
                        Implies(Call("PosDef", a), Equal(Call("CFCLog", a),
                            Call("intervalIntegral", Call("logPath", a), D(0), D(1))))))),
                    AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/Divergence/bhatia1997matrixanalysis")),
                    Blocks(Paragraph(Text(
                        "The scalar logarithm integral holds on the positive spectrum of A. "
                        + "Continuous functional calculus commutes with the integrable kernel "
                        + "integral and identifies its scalar inverse with the matrix inverse. "
                        + "Null endpoints connect the closed-interval set integral to the "
                        + "oriented interval integral from zero to one."))),
                    DescribeRole.Theorem),
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

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
