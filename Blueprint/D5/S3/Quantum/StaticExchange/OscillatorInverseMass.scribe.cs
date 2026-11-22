using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StaticExchange;

internal sealed class OscillatorInverseMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/StaticExchange/OscillatorInverseMass.";
    private static readonly Formula A = F.Id("a"), M = F.Id("m"), N = F.Id("n"), W = Omega;
    private static readonly Formula An = Seq(A, Underscore, N), Mn = Seq(M, Underscore, N);
    private static Formula At(string name) => Seq(F.Id(name), Open, W, Close);
    private static Formula Quot(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Kernel(Formula a, Formula m) =>
        Quot(a, Seq(m, Caret, D(2), Plus, W, Caret, D(2)));
    private static Formula Series(Formula term) => Seq(Sum, Underscore, Grp(N), Sp, term);
    private static Formula Integral(Formula term) => Seq(Int, Underscore, D(0), Caret, Grp(Infty),
        Sp, term, Thin, Sp, F.Id("d"), W);
    private static Formula Single()
    {
        var r = At("R");
        return Disp(Seq(D(0), Lt, M, Sp, Rightarrow, Sp, F.Id("R"), Sp, InMacro, Sp,
            F.Id("L"), Caret, D(1), Open, Mathbb, Grp(F.Id("R")), Close, Sp, Land, Sp,
            Integral(r), Eq, Quot(Pi, D(2)), Quot(A, M)));
    }
    private static Formula Criterion()
    {
        var mass = Integral(At("C"));
        var moment = Quot(An, Mn);
        return Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, N, Comma, An, Sp, Ge, Sp, D(0),
            Sp, Land, Sp, Mn, Gt, D(0), RowBreak, Amp, Rightarrow, Sp,
            mass, Eq, Series(Seq(Quot(Pi, D(2)), moment)), RowBreak,
            Amp, Land, Sp, Open, mass, Lt, Infty, Sp, Leftrightarrow, Sp, Series(moment), Lt, Infty, Close,
            End, Grp(F.Id("aligned"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Euclidean oscillator tower has finite integrated spectral weight on positive frequencies exactly when its residues divided by their masses form a summable family.",
        H("The inverse-mass criterion for finite equal-time fluctuations"),
        Blocks(
            Describe.Lean(DescribeId.Create("oscillator"), DeclarationHandle.Create(Prefix + "oscillator"),
                H("One oscillator response"), StatementSource.FromAuthor(Disp(Seq(At("R"), Eq, Kernel(A, M)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The real pole weight is a and the mass is m."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tower"), DeclarationHandle.Create(Prefix + "tower"),
                H("Nonnegative oscillator tower"), StatementSource.FromAuthor(Disp(Seq(At("C"), Eq,
                    Series(Seq(Max, Open, D(0), Comma, Kernel(An, Mn), Close))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each real term is mapped into the extended nonnegative reals before summation. For nonnegative residues and positive masses this preserves every term, including cases where the series totals infinity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-integral"), DeclarationHandle.Create(Prefix + "oscillator_integral"),
                H("The positive-frequency integral of a single mode"), StatementSource.FromAuthor(Single()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For m>0 and any real weight a, the substitution u=ω/m reduces the integral to the arctangent integral π/2. The mode is absolutely integrable on the entire real line."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inverse-mass"), DeclarationHandle.Create(Prefix + "tower_integral_criterion"),
                H("Sharp finiteness criterion for a positive tower"), StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Assume every mass is strictly positive and every residue is nonnegative. Tonelli's theorem integrates the countable nonnegative sum mode by mode, with infinite totals allowed. The constant π/2 is finite and positive, so the integrated response is finite exactly when the inverse-mass moment converges. The sequence may have repeated masses and arbitrarily small positive masses."))), DescribeRole.Theorem))));
}
