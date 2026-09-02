using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class FiniteZeckendorfEulerIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity.finite_zeckendorf_interval_and_euler";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded Zeckendorf names enumerate an initial Fibonacci interval and its finite Euler sum.",
        H("Finite Zeckendorf Euler Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-zeckendorf-interval-and-euler"),
            DeclarationHandle.Create(Declaration),
            H("Finite Zeckendorf names give the complete Fibonacci interval"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "GoldenName(Q) is the canonical carrier of admissible occupied indices from "
                        + "two through Q+1. Thus Q=N-1 relative to the source notation, and the "
                        + "source endpoint Fib(N+1) is Fib(Q+2).")),
                Paragraph(Text(
                    "The displayed exponent is constructed directly by summing the occupied "
                        + "Fibonacci weights. The proof identifies this source-defined map with "
                        + "the inverse of the existing canonical golden-name equivalence.")),
                Paragraph(Text(
                    "Reindexing the finite sum through that equivalence gives the initial-interval "
                        + "sum. The source-wide bound |x|<1 supplies x != 1 for the quotient form "
                        + "of the finite geometric series."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/GoldenNames")),
        ]));

    private static Formula Formula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula q = F.Id("Q");
        Formula x = F.Id("x");
        Formula name = F.Id("eta");
        Formula k = F.Id("k");
        Formula e = F.Id("e");
        Formula qPlusTwo = Seq(q, Sp, Plus, Sp, D(2));
        Formula fibCount = Call("Fib", qPlusTwo);
        Formula names = Call("GoldenName", q);
        Formula interval = Call("Fin", fibCount);
        Formula exponentMap = new Formula.Subscript(F.Id("E"), q);
        Formula fibValue = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, name), Sp, Call("Fib", k));
        Formula exponentDefinition = Seq(
            exponentMap, Colon, Sp, names, Sp, To, Sp, interval, Sp, Colon, Eq, Sp,
            Open, name, Colon, Sp, names, Sp, Mapsto, Sp, fibValue, Close);
        Formula exponent = Seq(exponentMap, Open, name, Close);
        Formula exponentNat = Seq(Open, exponent, Sp, Colon, Sp, naturals, Close);
        Formula nameSum = Seq(
            Sum, Underscore, Grp(name, Sp, InMacro, Sp, names), Sp,
            x, Caret, Grp(exponentNat));
        Formula intervalSum = Seq(
            Sum, Underscore, Grp(e, Sp, InMacro, Sp, interval), Sp,
            x, Caret, Grp(e));
        Formula quotient = Seq(
            Frac,
            Grp(D(1), Sp, Minus, Sp, x, Caret, Grp(fibCount)),
            Grp(D(1), Sp, Minus, Sp, x));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, q, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp, exponentDefinition, Semi,
            RowBreak, Grp(),
            Call("Bijective", exponentMap), Sp, Land, RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, reals, Comma, Sp,
            Lvert, Sp, x, Sp, Rvert, Sp, Lt, Sp, D(1), Sp, Rightarrow, RowBreak, Grp(),
            nameSum, Sp, Eq, Sp, intervalSum, Sp, Land, RowBreak, Grp(),
            intervalSum, Sp, Eq, Sp, quotient, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
