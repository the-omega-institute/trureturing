using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ThreeOutcomePermutationallyInvariantBellDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/aloy2024threeoutcomepibi");
    private const string Proposal =
        "To give a concrete example, we propose for any N > 3 the five 3PIBIs shown in Tab. III.";
    private const string Question =
        "At this point, for each conjectured inequality we have to prove that it is indeed valid for arbitrary number of parties N, or at least for all N larger than a minimum number.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five three-outcome PI Bell inequalities hold for every party count.",
        H("Three-outcome permutationally invariant Bell inequalities"),
        Blocks(
            Node("P1", "One-party PI observable", P1Formula(),
                "Section II, Eq. (3), p. 2: the one-party observable sums the marginal probability over all parties. There are N parties, two inputs and three outcomes. L is the finite hidden-variable type; w is its weight and p(l,i,x,a) is the local response. Outcome indices precede input indices in P1. All quantities are real.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("P2", "Two-party PI observable", P2Formula(),
                "Section II, Eq. (3), p. 2: the two-party observable sums over ordered pairs of distinct parties. The erased univ excludes i from the inner sum; no factor of one half is present. The response product belongs to the same hidden variable l. P2 takes its two outcomes before its two inputs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Pt0", "First symmetrized observable", SymFormula("Pt0", "P1",
                [[0, 0], [0, 1], [1, 0], [1, 1]]),
                "Equation (19), p. 5: Pt0 is the source's tilde P0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Pt00", "Equal outcomes at equal inputs", SymFormula("Pt00", "P2",
                [[0, 0, 0, 0], [0, 0, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]]),
                "Equation (19), p. 5: Pt00 is the source's tilde P00.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Pt01", "Different outcomes at different inputs", SymFormula("Pt01", "P2",
                [[0, 1, 0, 1], [1, 0, 0, 1]]),
                "Equation (19), p. 5: Pt01 is the source's tilde P01.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Pt10", "Equal outcomes at different inputs", SymFormula("Pt10", "P2",
                [[0, 0, 0, 1], [1, 1, 0, 1]]),
                "Equation (19), p. 5: Pt10 is the source's tilde P10.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Pt11", "Different outcomes at equal inputs", SymFormula("Pt11", "P2",
                [[0, 1, 0, 0], [0, 1, 1, 1]]),
                "Equation (19), p. 5: Pt11 is the source's tilde P11.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bell", "Bell expression", BellFormula(),
                "Equation (20), p. 5: the five coefficients multiply the five symmetrized observables, and the sixth entry is the additive classical-bound constant. The coefficient function c is indexed from zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("table", "The five Table III rows", TableFormula(),
                "Table III, p. 6, lists (alpha1, alpha2, alpha3, alpha4, alpha5, beta_c). Fin 5 numbers the source's rows 1 through 5 as 0 through 4. Each displayed vector is a function Fin 6 to Real, in exactly that coefficient order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Validity for arbitrary party number", ClaimFormula(),
                "Section III.A, p. 5, verbatim: " + Proposal + " " + Question +
                " The encoding quantifies over each row k and every N > 3, then over every finite hidden-variable type L and every normalized nonnegative w and p. Inputs are Fin 2, outcomes Fin 3 and parties Fin N. The finite-hidden-variable formulation is the finite convex-hull formulation of the local model; no integral representation theorem is asserted. The conclusion is nonnegativity of the literal Table III Bell expression.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All five Bell inequalities are valid", Disp(Call("claim")),
                "Every normalized finite local hidden-variable model satisfies all five inequalities. Independent local choices at both inputs give a distribution on deterministic strategies. The one-party and distinct-party two-party moments reproduce the responses, so the Bell expression is their weighted average. At a deterministic strategy, the nine outcome-pair counts give the Table II formulas. Row 2 is a square plus twice the joint count K. Row 3 separates the small marginal-count cases from a sum of squares and nonnegative products. Rows 4 and 5 reduce to a quadratic G on three natural numbers, nonnegative by the cases k = 0, k = 1 and k >= 2. The argument for the finite local model uses no lower bound on N; in particular it applies for every N >= 1. Validity alone asserts neither that these inequalities are facets nor that quantum correlations violate them.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("aloy-mullerrigat-tura-fadel-2024-three-outcome-pibi-validity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("three-outcome-pibi-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Op(string name)
    {
        var parts = name.Split('.');
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula Arguments(Formula[] args) =>
        Seq([.. args.SelectMany((a, i) => i == 0
            ? new[] { a } : new[] { Comma, Sp, a })]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Op(name) : Seq(Op(name), Parenthesized(Arguments(args)));
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Parenthesized(Arguments(args)));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(F.Id(name), type)), Comma, Sp, body);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Rightarrow, Sp, right);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Typed(F.Id(name), type)), Sp, Parenthesized(body));
    private static Formula Add(Formula[] terms) => Seq([.. terms.SelectMany((t, i) => i == 0
        ? new[] { t } : new[] { Sp, Plus, Sp, t })]);
    private static Formula Times(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Nonneg(Formula x) => Seq(D(0), Sp, Le, Sp, x);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Responses => Arrow(F.Id("L"), Arrow(Fin(F.Id("N")),
        Arrow(Fin(D(2)), Arrow(Fin(D(3)), Real))));
    private static Formula WithModel(Formula body) =>
        All("N", Nat, All("L", Call("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("L")), CloseBracket, Sp,
            All("w", Arrow(F.Id("L"), Real), All("p", Responses, body)))));
    private static Formula Observable(string name, params Formula[] indices) =>
        Call(name, [F.Id("w"), F.Id("p"), .. indices]);
    private static Formula Response(params Formula[] indices) => App(F.Id("p"), indices);

    private static Formula P1Formula() => Disp(WithModel(
        All("a", Fin(D(3)), All("x", Fin(D(2)), Equal(
            Observable("P1", F.Id("a"), F.Id("x")),
            SumOver("l", F.Id("L"), Times(App(F.Id("w"), F.Id("l")),
                SumOver("i", Fin(F.Id("N")), Response(
                    F.Id("l"), F.Id("i"), F.Id("x"), F.Id("a"))))))))));

    private static Formula P2Formula()
    {
        var l = F.Id("l"); var i = F.Id("i"); var j = F.Id("j");
        var a = F.Id("a"); var b = F.Id("b"); var x = F.Id("x"); var y = F.Id("y");
        Formula inner = Seq(new Formula.Subscript(Sum, Seq(Parenthesized(Typed(j, Fin(F.Id("N")))), Sp, InMacro, Sp, Call("Finset.erase", Call("Finset.univ"), i))), Sp, Parenthesized(Times(Response(l, i, x, a), Response(l, j, y, b))));
        return Disp(WithModel(All("a", Fin(D(3)), All("b", Fin(D(3)),
            All("x", Fin(D(2)), All("y", Fin(D(2)), Equal(
                Observable("P2", a, b, x, y), SumOver("l", F.Id("L"),
                    Times(App(F.Id("w"), l), SumOver("i", Fin(F.Id("N")), inner))))))))));
    }
    private static Formula SymFormula(string name, string baseName, byte[][] indices) =>
        Disp(WithModel(Equal(Observable(name), Add([.. indices.Select(row =>
            Observable(baseName, [.. row.Select(value => D(value))]))]))));

    private static Formula BellFormula() => Disp(WithModel(All("c", Arrow(Fin(D(6)), Real),
        Equal(Observable("bell", F.Id("c")), Add([
            Times(App(F.Id("c"), D(0)), Observable("Pt0")),
            Times(App(F.Id("c"), D(1)), Observable("Pt00")),
            Times(App(F.Id("c"), D(2)), Observable("Pt01")),
            Times(App(F.Id("c"), D(3)), Observable("Pt10")),
            Times(App(F.Id("c"), D(4)), Observable("Pt11")),
            App(F.Id("c"), D(5))])))));

    private static Formula TableFormula()
    {
        int[][] rows = [[1, 1, 0, -2, 0, 0], [1, 1, -2, -2, 2, 0],
            [-2, 1, 2, 2, 0, 4], [-6, 1, 4, 4, 2, 12], [-6, 1, 4, 0, 0, 24]];
        Formula Vector(Formula[] values) => Seq(Bang, OpenBracket, Arguments(values), CloseBracket);
        return Disp(Equal(Call("table"), Vector([.. rows.Select(row => Vector(
            [.. row.Select(n => n < 0 ? (Formula)new Formula.Negate(new Formula.Number(-n))
                : new Formula.Number(n))]))])));
    }

    private static Formula ClaimFormula()
    {
        var l = F.Id("l"); var i = F.Id("i"); var x = F.Id("x"); var a = F.Id("a");
        Formula wNonneg = All("l", F.Id("L"), Nonneg(App(F.Id("w"), l)));
        Formula wNorm = Equal(SumOver("l", F.Id("L"), App(F.Id("w"), l)), D(1));
        Formula pNonneg = All("l", F.Id("L"), All("i", Fin(F.Id("N")),
            All("x", Fin(D(2)), All("a", Fin(D(3)), Nonneg(Response(l, i, x, a))))));
        Formula pNorm = All("l", F.Id("L"), All("i", Fin(F.Id("N")), All("x", Fin(D(2)),
            Equal(SumOver("a", Fin(D(3)), Response(l, i, x, a)), D(1)))));
        Formula conclusion = Nonneg(Observable("bell", Call("table", F.Id("k"))));
        Formula models = All("L", Call("Type"), Seq(OpenBracket,
            Call("Fintype", F.Id("L")), CloseBracket, Sp,
            All("w", Arrow(F.Id("L"), Real), All("p", Responses,
                Imp(wNonneg, Imp(wNorm, Imp(pNonneg, Imp(pNorm, conclusion))))))));
        return Disp(Seq(Call("claim"), Sp, Leftrightarrow, Sp,
            All("k", Fin(D(5)), All("N", Nat, Imp(Seq(D(3), Sp, Lt, Sp, F.Id("N")), models)))));
    }
}
