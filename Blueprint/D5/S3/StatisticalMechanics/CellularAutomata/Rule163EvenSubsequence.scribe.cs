using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Rule163EvenSubsequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/hofmann2025rule163");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full integer-lattice evolution of Rule 163 from a single ON cell gives the even subsequence of OEIS A392003 and the closed form, two recurrences and generating function of A266753.",
        H("Rule 163 and the even subsequence of A392003"),
        Blocks(
            Node("rule", "Wolfram rule 163", RuleFormula(),
                "The output is bit 4l + 2c + r of 163, with false and true read as 0 and 1. In neighborhood order 111,110,101,100,011,010,001,000, the outputs are 1,0,1,0,0,0,1,1. The exterior is updated at every time step; both 000 and 111 produce 1.",
                "rule163", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sequence", "The cellular sequence A266753", SequenceFormula(),
                "OEIS A266753, NAME (revision 49, unpaginated): Decimal representation of the n-th iteration of the \"Rule 163\" elementary cellular automaton starting with a single ON (black) cell. The source program reads cells -n through n from left to right in base 2. The coordinate n-j has weight 2^j; row 0 has only its origin ON, and row is the existing evolution on all integer cells.",
                "A", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("explicit", "The explicit sequence A392003", ExplicitFormula(),
                "OEIS A392003, NAME (revision 30, unpaginated): a(n) = (7*2^n - 9 + 5*(-1)^n) / 6. The source offset is 1: only positive indices are used in the subsequence equation. The division is in the rational numbers.",
                "B", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The five source assertions", Disp(Iff(F.Id("claim"), ClaimBody())),
                SourceAssertions(), "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the five assertions", Disp(ClaimBody()),
                "For every positive time n, the entire row is 1 outside [-n,n], and the central word is 100 followed by n-1 copies of 10. Induction checks the three old neighbors at every integer coordinate, including the moving boundaries. Appending 10 multiplies the binary value by 4 and adds 2, so A(n+1)=4*A(n)+2 for n at least 1. Induction gives 6*A(n)+4=7*4^n; the rational closed form holds already at n=1. Substitution at even indices gives the subsequence identity, and eliminating the constant term from two successive first-order equations gives the second-order recurrence. Comparing coefficients of the formal power series uses A(0)=1, A(1)=4 and A(2)=18, then the second-order recurrence in every degree at least 3. The two denominator factors have constant term 1, so the product equation expresses the source rational generating function without analytic convergence assumptions.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static string SourceAssertions() =>
        "OEIS A392003, FORMULA (revision 30, unpaginated): Conjecture: a(2*n) = A266753(n). " +
        "OEIS A266753, FORMULA (revision 49, unpaginated): " +
        "Conjectures from _Colin Barker_, Jan 20 2016 and Apr 20 2019: (Start) " +
        "a(n) = 5*a(n-1)-4*a(n-2) for n>2. " +
        "G.f.: (1-x+2*x^2) / ((1-x)*(1-4*x)). " +
        "(End) " +
        "Empirical a(n) = (7*4^n - 4)/6 for n>1. - _Colin Barker_, Nov 25 2016 and Apr 20 2019 " +
        "a(n) = 4*a(n-1) + 2, n>1, conjectured. - _Yosu Yurramendi_, Jan 22 2017 " +
        "Here A is the cellular sequence, B is the explicit rational sequence, and n is natural. " +
        "The five clauses use n>=1, n>1, n>1, n>2, and all formal-series coefficients respectively. " +
        "Subtractions in the indices are natural subtraction; the second-order equation and series have integer coefficients.";

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("rule163-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(params string[] names) =>
        Seq(names.SelectMany((name, i) => i == 0
            ? new Formula[] { Named(name) }
            : new Formula[] { Dot, Named(name) }).ToArray());
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula AsRat(Formula value) => Typed(value, Rationals());
    private static Formula AsInt(Formula value) => Typed(value, Integers());

    private static Formula RuleFormula()
    {
        Formula l = F.Id("l"), c = F.Id("c"), r = F.Id("r");
        Formula ToNat(Formula x) => App(Qualified("Bool", "toNat"), x);
        Formula index = Add(Add(Multiply(D(4), ToNat(l)), Multiply(D(2), ToNat(c))), ToNat(r));
        return Disp(All("l", Named("Bool"), All("c", Named("Bool"), All("r", Named("Bool"),
            Equal(Call("rule163", l, c, r), App(Qualified("Nat", "testBit"), D(1, 6, 3), index))))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j");
        Formula row = App(Qualified("D5", "S0", "Automata", "RuleThirtyTwentyTwoMersenneSignRefutation", "row"),
            Named("rule163"), n, Subtract(AsInt(n), AsInt(j)));
        Formula summand = Multiply(App(Qualified("Bool", "toNat"), row), Pow(D(2), j));
        Formula range = App(Qualified("Finset", "range"), Add(Multiply(D(2), n), D(1)));
        return Disp(All("n", Naturals(), Equal(Call("A", n),
            Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, range), Sp, summand))));
    }

    private static Formula ExplicitFormula()
    {
        Formula m = F.Id("m");
        Formula numerator = Add(Subtract(Multiply(D(7), Pow(AsRat(D(2)), m)), D(9)),
            Multiply(D(5), Pow(AsRat(new Formula.Negate(D(1))), m)));
        return Disp(All("m", Naturals(), Equal(Call("B", m), new Formula.Fraction(numerator, D(6)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula even = All("n", Naturals(), Imp(Le(D(1), n),
            Equal(Call("B", Multiply(D(2), n)), AsRat(Call("A", n)))));
        Formula closed = All("n", Naturals(), Imp(Lt(D(1), n), Equal(AsRat(Call("A", n)),
            new Formula.Fraction(Subtract(Multiply(D(7), Pow(AsRat(D(4)), n)), D(4)), D(6)))));
        Formula first = All("n", Naturals(), Imp(Lt(D(1), n), Equal(Call("A", n),
            Add(Multiply(D(4), Call("A", Subtract(n, D(1)))), D(2)))));
        Formula second = All("n", Naturals(), Imp(Lt(D(2), n), Equal(AsInt(Call("A", n)),
            Subtract(Multiply(D(5), AsInt(Call("A", Subtract(n, D(1))))),
                Multiply(D(4), AsInt(Call("A", Subtract(n, D(2)))))))));
        Formula x = Qualified("PowerSeries", "X");
        Formula series = App(Qualified("PowerSeries", "mk"),
            Seq(Named("fun"), Sp, Typed(n, Naturals()), Sp, Mapsto, Sp, AsInt(Call("A", n))));
        Formula denominator = Multiply(Parenthesized(Subtract(D(1), x)),
            Parenthesized(Subtract(D(1), Multiply(D(4), x))));
        Formula generating = Equal(Multiply(series, Parenthesized(denominator)),
            Add(Subtract(D(1), x), Multiply(D(2), Pow(x, D(2)))));
        return And(even, And(closed, And(first, And(second, generating))));
    }
}
