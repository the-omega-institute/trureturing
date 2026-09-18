using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class CumulativeCountHeatBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monotone cumulative geometric counts give all positive time summability and two-sided small-time heat bounds.",
        H("Cumulative count heat bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cumulative-count-heat-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds."
                        + "cumulative_count_heat_bounds"),
                H("The scalar heat estimate from cumulative counts"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be a monotone natural-valued cumulative count with N(0)=1. "
                            + "Assume positive constants c_minus and c_plus and bases lambda,q greater "
                            + "than one sandwich every N(L) between c_minus lambda^L and c_plus lambda^L.")),
                    Paragraph(Text(
                        "Define the natural increments by subtraction, the zero mode a(0)=0 and "
                            + "a(L)=q^L for L>0, and let F_t(L) be the increment weighted by "
                            + "exp(-t a(L)). The exponent gamma is log(lambda)/log(q); U is the "
                            + "convergent superexponential tail sum of lambda^(k+1) exp(-q^k).")),
                    Paragraph(Text(
                        "For every positive t the scalar series is summable. For 0<t<=1, its "
                            + "sum lies between C_minus t^(-gamma) and C_plus t^(-gamma), where "
                            + "C_minus=c_minus/(exp(1) lambda) and C_plus=c_plus(1+U). The proof "
                            + "uses only cumulative counts, so zero increments and plateaus are allowed."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula N = F.Id("N");
        Formula cm = F.Id("cminus");
        Formula cp = F.Id("cplus");
        Formula lam = F.Id("lambda");
        Formula q = F.Id("q");
        Formula L = F.Id("L");
        Formula t = F.Id("t");
        Formula gamma = F.Id("gamma");
        Formula S = F.Id("S");
        Formula Cminus = F.Id("Cminus");
        Formula Cplus = F.Id("Cplus");
        Formula positive = Seq(D(0), Sp, Lt, Sp, cm, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, cp, Sp, Land, Sp,
            D(1), Sp, Lt, Sp, lam, Sp, Land, Sp,
            D(1), Sp, Lt, Sp, q);
        Formula count = Seq(Forall, Sp, L, Colon, Sp, natural, Comma, Sp,
            cm, Sp, Times, Sp, Pow(lam, L), Sp, Leq, Sp, Call("NatCast", Call("N", L)),
            Sp, Land, Sp, Call("NatCast", Call("N", L)), Sp, Leq, Sp,
            cp, Sp, Times, Sp, Pow(lam, L));
        Formula conclusion = Seq(
            Open, D(0), Sp, Lt, Sp, gamma, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Cminus, Sp, Land, Sp, D(0), Sp, Lt, Sp, Cplus, Close,
            Sp, Land, Sp,
            Forall, Sp, t, Colon, Sp, real, Comma, Sp, D(0), Sp, Lt, Sp, t,
            Sp, Rightarrow, Sp, Call("Summable", F.Id("Ft")), Sp, Land, Sp,
            Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Land, Sp, t, Sp, Leq, Sp, D(1),
            Sp, Rightarrow, Sp,
            Cminus, Sp, Times, Sp, Pow(t, Seq(Minus, gamma)), Sp, Leq, Sp, Call("S", t),
            Sp, Land, Sp, Call("S", t), Sp, Leq, Sp,
            Cplus, Sp, Times, Sp, Pow(t, Seq(Minus, gamma)));
        return Disp(Seq(
            Forall, Sp, N, Colon, Sp, natural, Comma, Sp,
            Forall, Sp, cm, Comma, Sp, cp, Comma, Sp, lam, Comma, Sp, q,
            Colon, Sp, real, Comma, Sp,
            Open, Call("Monotone", N), Sp, Land, Sp, Call("N", D(0)), Sp, Eq, Sp, D(1), Sp,
            Land, Sp, positive, Sp, Land, Sp, count, Close,
            Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
