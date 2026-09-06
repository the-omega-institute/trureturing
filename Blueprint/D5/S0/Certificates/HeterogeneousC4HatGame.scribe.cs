using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class HeterogeneousC4HatGameDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S0/Certificates/HeterogeneousC4HatGame.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit legal strategies win two heterogeneous four-cycle hat games.",
        H("Heterogeneous C4 Hat Games"),
        Blocks(
            Paragraph(Text(
                "The coordinates 0, 1, 2, 3 denote A, B, Z, Omega in that order. "
                    + "The undirected cycle is A-B-Z-Omega-A: A and Z each see B and Omega. "
                    + "The parameter functions h and g give the number of available colours "
                    + "and the exact number of distinct guesses at each vertex. "
                    + "Fin(n) consists of the integers from zero through n minus one.")),
            Paragraph(Text(
                "McInnis, arXiv:2507.21487v1, Section 1.1 and Question 7.1.8(1), "
                    + "supplies the Czech game and the open question. The definitions below "
                    + "are this repository's coordinate representation of its C4 restriction; "
                    + "the two explicit winning strategies and their finite coverage proofs "
                    + "are repository constructions.")),
            Definition("LocalPlan", "local-plan", "Legal local plans", LocalPlanFormula(),
                "The input contains exactly the colours at left and right. The output is "
                    + "a finite subset of the vertex's own colour type, together with a proof "
                    + "that its cardinality is exactly g(v)."),
            Definition("Coloring", "coloring", "All four-vertex colourings", ColoringFormula(),
                "The Cartesian product is associated to the right, as in Lean."),
            Definition("Strategy", "strategy", "Legal C4 strategies", StrategyFormula(),
                "The product is associated to the right. "
                    + "Their ordered inputs are (B,Omega), (A,Z), (B,Omega), (Z,A)."),
            Definition("GuessesCorrectly", "guesses-correctly", "Correct guesses at each vertex",
                CorrectFormula(),
                "The bracketed four-vector is the function on Fin(4) with these entries "
                    + "in coordinate order. Applying it at v selects entry v. "
                    + "The operator val forgets the cardinality proof in a local-plan output."),
            Definition("Wins", "wins", "A strategy wins every colouring", WinsFormula(),
                "The strategy is fixed before the colouring is chosen. The correctly "
                    + "guessing vertex may depend on the colouring."),
            Definition("Winnable", "winnable", "Existence of a winning strategy", WinnableFormula(),
                "A game is winnable when some tuple of legal local plans wins every colouring."),
            Describe.Example(
                DescribeId.Create("strategy-three-four-four-three"),
                H("A strategy for hatness (3,4,4,3)"),
                StrategyWitnessFormula(3),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bound witness s is the private Lean strategy3443. Its A table has "
                        + "input Fin(4) times Fin(3) and returns two-element subsets of Fin(3). "
                        + "Its B table has input Fin(3) times Fin(4) and output Fin(4); "
                        + "its Z table has input Fin(4) times Fin(3) and output Fin(4); "
                        + "its Omega table has input Fin(4) times Fin(3) and output Fin(3). "
                        + "The B, Z, and Omega outputs become singleton subsets. The subtype "
                        + "proofs certify guessness (2,1,1,1), and the private coordinate "
                        + "coverage proposition is checked by kernel decide on all 144 colourings.")))),
            Describe.Example(
                DescribeId.Create("strategy-three-four-four-four"),
                H("A strategy for hatness (3,4,4,4)"),
                StrategyWitnessFormula(4),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bound witness s is the private Lean strategy3444. Its A table has "
                        + "input Fin(4) times Fin(4) and returns two-element subsets of Fin(3). "
                        + "Its B table has input Fin(3) times Fin(4) and output Fin(4); "
                        + "its Z table has input Fin(4) times Fin(4) and output Fin(4); "
                        + "its Omega table has input Fin(4) times Fin(3) and output Fin(4). "
                        + "The B, Z, and Omega outputs become singleton subsets. The subtype "
                        + "proofs certify guessness (2,1,1,1), and the private coordinate "
                        + "coverage proposition is checked by kernel decide on all 192 colourings.")))),
            Describe.Lean(
                DescribeId.Create("c4-three-four-winnable"),
                DeclarationHandle.Create(Root + "c4_three_four_winnable"),
                H("Two winning C4 instances"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both conjuncts use source order A,B,Z,Omega and guessness (2,1,1,1). "
                            + "The first has hatness (3,4,4,3); the second has hatness (3,4,4,4). "
                            + "Each tuple denotes its coordinate function on Fin(4).")),
                    Paragraph(Text(
                        "The proof supplies the two explicit legal strategies. At A the table "
                            + "entries are two-element subsets; at B, Z, and Omega the entries "
                            + "are single colours, used as singleton subsets. Kernel decide "
                            + "checks the two private coordinate coverage propositions on all "
                            + "144 and 192 colourings respectively. The Boolean membership "
                            + "checks are proved equivalent to GuessesCorrectly.")),
                    Paragraph(Text(
                        "This proves only the two positive C4 cases. The negative direction "
                            + "with hatness four at A has only external DRAT verification in "
                            + "the source-aligned probe; it has no kernel theorem here. "
                            + "No result is asserted for cycles with at least five vertices."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Separated(params Formula[] values)
    {
        var items = new List<Formula>();
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] values) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Separated(values)));

    private static Formula Tuple(params Formula[] values) => Parenthesized(Separated(values));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Vertex() => Fin(D(4));
    private static Formula FunctionType() => Seq(Vertex(), Sp, To, Sp, F.Id("Nat"));
    private static Formula Parameters() =>
        Seq(Forall, Sp, F.Id("h"), Comma, Sp, F.Id("g"), Colon, Sp, FunctionType(), Comma);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma);

    private static Formula LocalPlanFormula()
    {
        Formula h = F.Id("h"), g = F.Id("g"), v = F.Id("v");
        Formula left = F.Id("left"), right = F.Id("right"), guesses = F.Id("guesses");
        return Disp(new Formula.Aligned([
            Parameters(),
            Seq(Forall, Sp, v, Comma, Sp, left, Comma, Sp, right, Colon, Sp, Vertex(), Comma),
            Seq(Call("LocalPlan", h, g, v, left, right), Sp, Eq, Sp,
                Parenthesized(Seq(
                    Parenthesized(Seq(Fin(Call("h", left)), Sp, Times, Sp, Fin(Call("h", right)))),
                    Sp, To, Sp,
                    OpenBrace, guesses, Colon, Sp, Call("Finset", Fin(Call("h", v))),
                    Sp, Mid, Sp, Call("card", guesses), Sp, Eq, Sp, Call("g", v), CloseBrace)), Dot),
        ]));
    }

    private static Formula ColoringFormula() => Disp(new Formula.Aligned([
        Bound("h", FunctionType()),
        Seq(Call("Coloring", F.Id("h")), Sp, Eq, Sp,
            Fin(Call("h", D(0))), Sp, Times, Sp, Fin(Call("h", D(1))), Sp, Times, Sp,
            Fin(Call("h", D(2))), Sp, Times, Sp, Fin(Call("h", D(3))), Dot),
    ]));

    private static Formula StrategyFormula() => Disp(new Formula.Aligned([
        Parameters(),
        Seq(Call("Strategy", F.Id("h"), F.Id("g")), Sp, Eq, Sp,
            Call("LocalPlan", F.Id("h"), F.Id("g"), D(0), D(1), D(3)), Sp, Times),
        Seq(Call("LocalPlan", F.Id("h"), F.Id("g"), D(1), D(0), D(2)), Sp, Times, Sp,
            Call("LocalPlan", F.Id("h"), F.Id("g"), D(2), D(1), D(3)), Sp, Times),
        Seq(Call("LocalPlan", F.Id("h"), F.Id("g"), D(3), D(2), D(0)), Dot),
    ]));

    private static Formula Proj(Formula value, byte field) => Seq(value, Dot, D(field));

    private static Formula CorrectEntry(Formula own, Formula plan, Formula left, Formula right) =>
        Seq(own, Sp, InMacro, Sp,
            Call("val", Seq(Parenthesized(plan), Parenthesized(Tuple(left, right)))));

    private static Formula CorrectFormula()
    {
        Formula c = F.Id("c"), s = F.Id("s");
        Formula cA = Proj(c, 1), cB = Proj(Proj(c, 2), 1);
        Formula cZ = Proj(Proj(Proj(c, 2), 2), 1), cO = Proj(Proj(Proj(c, 2), 2), 2);
        Formula sA = Proj(s, 1), sB = Proj(Proj(s, 2), 1);
        Formula sZ = Proj(Proj(Proj(s, 2), 2), 1), sO = Proj(Proj(Proj(s, 2), 2), 2);
        return Disp(new Formula.Aligned([
        Parameters(),
        Bound("s", Call("Strategy", F.Id("h"), F.Id("g"))),
        Bound("c", Call("Coloring", F.Id("h"))),
        Seq(Call("GuessesCorrectly", F.Id("h"), F.Id("g"), F.Id("s"), F.Id("c")), Sp, Eq, Sp,
            OpenBracket,
            CorrectEntry(cA, sA, cB, cO), Comma, Sp,
            CorrectEntry(cB, sB, cA, cZ), Comma),
        Seq(CorrectEntry(cZ, sZ, cB, cO), Comma, Sp,
            CorrectEntry(cO, sO, cZ, cA), CloseBracket, Dot),
        ]));
    }

    private static Formula StrategyWitnessFormula(byte last)
    {
        Formula h = Tuple(D(3), D(4), D(4), D(last));
        Formula g = Tuple(D(2), D(1), D(1), D(1));
        return Disp(Seq(Exists, Sp, F.Id("s"), Colon, Sp, Call("Strategy", h, g),
            Comma, Sp, Call("Wins", h, g, F.Id("s"))));
    }

    private static Formula WinsFormula() => Disp(new Formula.Aligned([
        Parameters(),
        Bound("s", Call("Strategy", F.Id("h"), F.Id("g"))),
        Seq(Call("Wins", F.Id("h"), F.Id("g"), F.Id("s")), Sp, Iff, Sp,
            Parenthesized(Seq(
                Forall, Sp, F.Id("c"), Colon, Sp, Call("Coloring", F.Id("h")), Comma, Sp,
                Exists, Sp, F.Id("v"), Colon, Sp, Vertex(), Comma, Sp,
                Call("GuessesCorrectly", F.Id("h"), F.Id("g"), F.Id("s"), F.Id("c"), F.Id("v")))), Dot),
    ]));

    private static Formula WinnableFormula() => Disp(new Formula.Aligned([
        Parameters(),
        Seq(Call("Winnable", F.Id("h"), F.Id("g")), Sp, Iff, Sp,
            Parenthesized(Seq(
                Exists, Sp, F.Id("s"), Colon, Sp, Call("Strategy", F.Id("h"), F.Id("g")), Comma, Sp,
                Call("Wins", F.Id("h"), F.Id("g"), F.Id("s")))), Dot),
    ]));

    private static Formula TheoremFormula() => Disp(Seq(
        Parenthesized(Call("Winnable", Tuple(D(3), D(4), D(4), D(3)),
            Tuple(D(2), D(1), D(1), D(1)))),
        Sp, Land, Sp,
        Parenthesized(Call("Winnable", Tuple(D(3), D(4), D(4), D(4)),
            Tuple(D(2), D(1), D(1), D(1)))), Dot));
}
