using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OriginalHalfBinomialPeriod.";
    private static Formula ComplexNumbers => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Derivative(Formula f) => Call("deriv", f);

    private static Formula PeriodFormula()
    {
        var z = F.Id("z");
        var n = F.Id("n");
        return Disp(Seq(Forall, Sp, z, InMacro, Sp, ComplexNumbers, Comma, Sp,
            Call("period", z), Eq, Sum, Underscore, Grp(n, Eq, D(0)),
            Caret, Grp(Infty), Call("halfBinomial", n), Caret, Grp(D(2)),
            z, Caret, Grp(n)));
    }

    private static Formula PicardFuchsFormula()
    {
        var z = F.Id("z");
        var f = F.Id("period");
        var df = Derivative(f);
        var ddf = Derivative(df);
        return Disp(Seq(Forall, Sp, z, InMacro, Sp, ComplexNumbers, Comma, Sp,
            Vert, Sp, z, Sp, Vert, Lt, D(1), Rightarrow, Sp,
            Call("DifferentiableAt", ComplexNumbers, f, z), Land, Sp,
            Call("DifferentiableAt", ComplexNumbers, df, z), Land, Sp,
            z, Open, D(1), Minus, z, Close, Open, ddf, Close, Open, z, Close,
            Plus, Open, D(1), Minus, D(2), z, Close, Open, df, Close, Open, z, Close,
            Minus, Frac, Grp(D(1)), Grp(D(4)), Call("period", z), Eq, D(0)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complex analytic period of the original half-binomial coefficients.",
        H("The original period equation"), Blocks(
            Describe.Lean(DescribeId.Create("original-half-binomial-period"),
                DeclarationHandle.Create(Prefix + "period"), H("The actual period"),
                StatementSource.FromAuthor(PeriodFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z the period is the infinite sum of halfBinomial(n) squared times z to the n. The coefficient halfBinomial(n) is the original product of -1/2-j for 0 <= j < n divided by n factorial. The definition uses the complex sum, with the usual totalized value when a series is not summable. All convergence and differential claims below are restricted to the open unit disk."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-half-binomial-period-picard-fuchs"),
                DeclarationHandle.Create(Prefix + "picard_fuchs"), H("The full complex disk equation"),
                StatementSource.FromAuthor(PicardFuchsFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At every complex z of norm less than one, both the period and its first complex derivative are complex differentiable, and z(1-z) times its second derivative plus (1-2z) times its first derivative minus one quarter times the period equals zero. Zero is included; the argument never divides by z.")),
                    Paragraph(Text("The original successor recurrence gives the exact square-coefficient recurrence (n+1)^2 c(n+1)=(n+1/2)^2 c(n) and bounds the coefficient norms by one. On any smaller disk, polynomially weighted geometric series dominate the original and shifted derivative series. The complex locally uniform series theorems justify differentiation twice. Reindexing these convergent sums identifies the two sides coefficient by coefficient.")),
                    Paragraph(Text("The equation is the classical Gauss hypergeometric differential equation with a=b=1/2 and c=1, as in DLMF 15.10.1. The result here establishes it for the literal original factorial-product coefficients over the full complex unit disk. It does not identify a native operator resolvent, determine a boundary logarithmic constant or nome, or establish a conformal field theory or string realization."))),
                DescribeRole.Theorem))));
}
