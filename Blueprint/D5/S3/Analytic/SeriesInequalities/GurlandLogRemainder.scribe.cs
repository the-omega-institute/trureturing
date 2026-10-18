using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class GurlandLogRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/AnalyticClosure/wisniewska2025gurland");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Gurland logarithmic remainder tends to zero for every positive real pair.",
        H("Gurland Logarithmic Remainder"),
        Blocks(
            Entry("hurwitz", "sourceHurwitz", "The source Hurwitz series", Hurwitz(),
                "The index j ranges over natural numbers starting at zero. The exponent s is natural. "
                + "In the expansion s=2k with k at least one, and the shift b=1+(x+y)/2 is strictly greater than one. "
                + "The proof establishes summability on this domain by comparison with the shifted p-series. "
                + "The shift is the actual real shift in equation (3); it is not reduced modulo one.", DescribeRole.Definition, true),
            Entry("gamma-ratio", "gammaRatio", "The modified Gamma ratio", Ratio(),
                "This is equation (2), with the positive-real Gamma function. "
                + "Its denominator is positive whenever x and y are positive, including positive integer arguments.",
                DescribeRole.Definition, true),
            Entry("partial-expansion", "partialExpansion", "The finite Hurwitz expansion", Partial(),
                "The finite interval Ico(1,m) contains exactly the integers k with 1 <= k < m. "
                + "This is the original S_m, with no restriction involving Q(x,y).", DescribeRole.Definition, true),
            Entry("remainder", "remainder", "The original remainder", Remainder(),
                "Equation (4) determines the remainder as log(gammaRatio(x,y))-partialExpansion(x,y,m). "
                + "The n in the source notation R_n^m is already summed out. "
                + "This definition also determines the diagonal value without choosing a point in an empty Taylor interval.",
                DescribeRole.Definition, true),
            Entry("claim", "claim", "The whole positive-pair question", Claim(),
                "Open Problem 1 asks: In Corollary 1 we showed that R_n^m(x,y) tends to zero under a sufficient condition. "
                + "Does R_n^m(x,y) tend to zero hold for every x,y > 0? "
                + "The limit is in the natural expansion order m, with the source using m >= 2. "
                + "Tendsto uses the atTop filter on natural m and the neighbourhood filter of zero in the reals.",
                DescribeRole.Definition, true),
            Entry("result", "result", "The remainder converges on the whole domain", Disp(V("claim")),
                "Put a=(x+y)/2, d=(x-y)/2 and c_n=d^2/(n+1+a)^2. Positivity gives 0 <= c_n < 1. "
                + "The positive-real Euler limit at 1+x, 1+y and 1+a cancels the factorial and logarithmic terms. "
                + "It identifies log(gammaRatio(x,y)) with the sum of -log(1-c_n). "
                + "The nonnegative logarithmic power series is jointly summable, so its two sums can be exchanged. "
                + "Each coefficient is exactly d^(2k) times the source Hurwitz series divided by k. "
                + "Finite interchange identifies the source partial expansions, and their limit gives the stated remainder limit. "
                + "For x=y the ratio is one and every partial sum and remainder is zero. "
                + "The convergence is pointwise for every positive pair; no uniform rate on the unbounded quadrant is asserted. "
                + "Open Problem 2 is the equivalent series identity. Open Problem 3 is not settled. "
                + "The Euler limit, logarithmic power series, p-series comparison and summation theorems are classical tools. "
                + "No priority claim is made; the full-text overlap with Merkle's 2005 paper remains unverified.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("wisniewska-2025-gurland-remainder"), ResolutionKind.Proved) : null);

    private static Formula V(string s) => F.Id(s);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, body);
    private static Formula Call(string n, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula A => Div(Add(V("x"), V("y")), D(2));
    private static Formula Delta => Div(Sub(V("x"), V("y")), D(2));
    private static Formula Sum(Formula index, Formula body) => Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Hurwitz() => Disp(All("s", Nat, All("b", Real,
        Eqn(Call("sourceHurwitz", V("s"), V("b")), Sum(Seq(V("j"), Sp, InMacro, Sp, Nat),
            Div(D(1), Pow(Add(V("j"), V("b")), V("s"))))))));
    private static Formula Ratio() => Disp(All("x", Real, All("y", Real,
        Eqn(Call("gammaRatio", V("x"), V("y")), Div(
            Mul(Call("Gamma", Add(D(1), V("x"))), Call("Gamma", Add(D(1), V("y")))),
            Pow(Call("Gamma", Add(D(1), A)), D(2)))))));
    private static Formula Partial() => Disp(All("x", Real, All("y", Real, All("m", Nat,
        Eqn(Call("partialExpansion", V("x"), V("y"), V("m")),
            Sum(Seq(V("k"), Sp, InMacro, Sp, Call("Ico", D(1), V("m"))),
                Div(Mul(Pow(Seq(Open, Delta, Close), Mul(D(2), V("k"))),
                    Call("sourceHurwitz", Mul(D(2), V("k")), Add(D(1), A))), V("k"))))))));
    private static Formula Remainder() => Disp(All("x", Real, All("y", Real, All("m", Nat,
        Eqn(Call("remainder", V("x"), V("y"), V("m")),
            Sub(Call("log", Call("gammaRatio", V("x"), V("y"))),
                Call("partialExpansion", V("x"), V("y"), V("m"))))))));
    private static Formula Claim() => Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff,
        All("x", Real, All("y", Real, Seq(
            D(0), Lt, V("x"), Sp, Implies, Sp, D(0), Lt, V("y"), Sp, Implies, Sp,
            Call("Tendsto", Call("remainder", V("x"), V("y")), V("atTop"), Call("nhds", D(0))))))));
}
