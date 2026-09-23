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
                        "Let N: Nat -> Nat be a monotone cumulative count with N(0)=1. "
                            + "Assume positive real constants cminus and cplus and real bases lambda,q "
                            + "greater than one sandwich every N(L) between cminus lambda^L and "
                            + "cplus lambda^L. NatCast denotes the inclusion of natural numbers into the reals.")),
                    Paragraph(Text(
                        "Define m: Nat -> Nat by m(0)=1 and m(k+1)=N(k+1)-N(k) for every "
                            + "natural k, using natural subtraction (truncated at zero). Define "
                            + "a: Nat -> Real by a(0)=0 and a(k+1)=q^(k+1) for every natural k.")),
                    Paragraph(Text(
                        "For real t and natural L, define F(t,L)=NatCast(m(L))*exp(-t*a(L)), "
                            + "and define S(t) as the infinite sum of F(t,L) over all natural L, "
                            + "including L=0. Set gamma=log(lambda)/log(q). For natural k, put "
                            + "u(k)=lambda^(k+1)*exp(-(q^k)); U is the infinite sum of u(k) over "
                            + "all natural k, including k=0. This superexponential tail series converges. "
                            + "Set Cminus=cminus/(exp(1)*lambda) and Cplus=cplus*(1+U).")),
                    Paragraph(Text(
                        "For every positive t the scalar series is summable. For 0<t<=1, its "
                            + "sum S(t) lies between Cminus*t^(-gamma) and Cplus*t^(-gamma), "
                            + "with the same constants for all such t and with real powers. The proof "
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
        Formula k = F.Id("k");
        Formula t = F.Id("t");
        Formula gamma = F.Id("gamma");
        Formula Cminus = F.Id("Cminus");
        Formula Cplus = F.Id("Cplus");
        Formula U = F.Id("U");
        Formula successor = Seq(k, Sp, Plus, Sp, D(1));
        Formula definitions = Seq(
            Call("m", D(0)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Open, Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            Call("m", successor), Sp, Eq, Sp, Call("N", successor), Sp,
            Minus, Underscore, Grp(natural), Sp, Call("N", k), Close,
            Sp, Land, Sp, Call("a", D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Open, Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            Call("a", successor), Sp, Eq, Sp, Pow(q, successor), Close,
            RowBreak, Nl, Amp, Quad, Land, Sp,
            gamma, Sp, Eq, Sp, Frac, Grp(Call("log", lam)), Grp(Call("log", q)),
            Sp, Land, Sp, Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            Forall, Sp, L, Colon, Sp, natural, Comma, Sp,
            Call("F", t, L), Sp, Eq, Sp, Call("NatCast", Call("m", L)), Sp, Times, Sp,
            Call("exp", Seq(Minus, t, Sp, Times, Sp, Call("a", L))), Close,
            RowBreak, Nl, Amp, Quad, Land, Sp,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            Call("S", t), Sp, Eq, Sp, Sum, Apos, Underscore, Grp(L, Colon, Sp, natural),
            Sp, Call("F", t, L), Close, Sp, Land, Sp,
            Open, Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            Call("u", k), Sp, Eq, Sp, Pow(lam, successor), Sp, Times, Sp,
            Call("exp", Seq(Minus, Pow(q, k))), Close,
            RowBreak, Nl, Amp, Quad, Land, Sp,
            U, Sp, Eq, Sp, Sum, Apos, Underscore, Grp(k, Colon, Sp, natural), Sp, Call("u", k),
            Sp, Land, Sp, Cminus, Sp, Eq, Sp,
            Frac, Grp(cm), Grp(Call("exp", D(1)), Sp, Times, Sp, lam),
            Sp, Land, Sp, Cplus, Sp, Eq, Sp, cp, Sp, Times, Sp,
            Open, D(1), Sp, Plus, Sp, U, Close);
        Formula positive = Seq(D(0), Sp, Lt, Sp, cm, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, cp, Sp, Land, Sp,
            D(1), Sp, Lt, Sp, lam, Sp, Land, Sp,
            D(1), Sp, Lt, Sp, q);
        Formula count = Seq(Open, Forall, Sp, L, Colon, Sp, natural, Comma, Sp, Open,
            cm, Sp, Times, Sp, Pow(lam, L), Sp, Leq, Sp, Call("NatCast", Call("N", L)),
            Sp, Land, Sp, Call("NatCast", Call("N", L)), Sp, Leq, Sp,
            cp, Sp, Times, Sp, Pow(lam, L), Close, Close);
        Formula conclusion = Seq(
            Open,
            Open, D(0), Sp, Lt, Sp, gamma, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Cminus, Sp, Land, Sp, D(0), Sp, Lt, Sp, Cplus, Close,
            RowBreak, Nl, Amp, Quad, Land, Sp,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp, D(0), Sp, Lt, Sp, t,
            Sp, Rightarrow, Sp, Call("Summable", Seq(L, Colon, Sp, natural,
                Sp, Mapsto, Sp, Call("F", t, L))), Close,
            RowBreak, Nl, Amp, Quad, Land, Sp,
            Open, Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, t, Sp, Land, Sp, t, Sp, Leq, Sp, D(1), Close,
            Sp, Rightarrow, Sp, Open,
            Cminus, Sp, Times, Sp, Pow(t, Seq(Minus, gamma)), Sp, Leq, Sp, Call("S", t),
            Sp, Land, Sp, Call("S", t), Sp, Leq, Sp,
            Cplus, Sp, Times, Sp, Pow(t, Seq(Minus, gamma)), Close, Close, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("aligned")), Nl, Amp,
            Forall, Sp, N, Colon, Sp, natural, Sp, To, Sp, natural, Comma, Sp,
            Forall, Sp, cm, Comma, Sp, cp, Comma, Sp, lam, Comma, Sp, q,
            Colon, Sp, real, Comma, Sp,
            RowBreak, Nl, Amp,
            Forall, Sp, F.Id("m"), Colon, Sp, natural, Sp, To, Sp, natural, Comma, Sp,
            Forall, Sp, F.Id("a"), Comma, Sp, F.Id("u"), Colon, Sp,
            natural, Sp, To, Sp, real, Comma, Sp,
            RowBreak, Nl, Amp,
            Forall, Sp, F.Id("F"), Colon, Sp, real, Sp, To, Sp, natural, Sp, To, Sp, real, Comma, Sp,
            Forall, Sp, F.Id("S"), Colon, Sp, real, Sp, To, Sp, real, Comma, Sp,
            RowBreak, Nl, Amp,
            Forall, Sp, gamma, Comma, Sp, U, Comma, Sp, Cminus, Comma, Sp, Cplus,
            Colon, Sp, real, Comma,
            RowBreak, Nl, Amp,
            Open, Call("Monotone", N), Sp, Land, Sp, Call("N", D(0)), Sp, Eq, Sp, D(1), Sp,
            Land, Sp, positive,
            RowBreak, Nl, Amp, Quad, Land, Sp, count,
            RowBreak, Nl, Amp, Quad, Land, Sp, definitions, Close,
            RowBreak, Nl, Amp, Rightarrow, Sp, conclusion, Dot, Nl,
            End, Grp(F.Id("aligned"))));
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
