using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class BarkerCyclicRepetitionCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/barker2019a268943");
    private const string NameQuote =
        "OEIS A268943, revision 8, unpaginated NAME (%N): \"Number of length-n 0..7 arrays "
        + "with no repeated value unequal to the previous repeated value plus one mod 7+1.\" ";
    private const string FormulaQuote =
        "OEIS A268943, revision 8, unpaginated FORMULA (%F): "
        + "\"Conjectures from _Colin Barker_, Jan 17 2019: (Start)\" "
        + "\"G.f.: 8*x*(1 - 5*x - 7*x^2) / ((1 - 7*x)*(1 - 6*x - 8*x^2)).\" "
        + "\"a(n) = (-272*7^n + (153-37*sqrt(17))*(3-sqrt(17))^n + "
        + "(3+sqrt(17))^n*(153+37*sqrt(17))) / 34.\" \"(End)\" ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function and radical formula count cyclic repetition words.",
        H("Cyclic successive repetitions over eight letters"),
        Blocks(
            Paragraph(Text("Letters lie in Fin 8. Positions in Fin n are zero based. "
                + "An event is an adjacent equal pair, and overlapping pairs are retained. "
                + "The source offset is 1,1: its generating series has zero constant coefficient. "
                + "The count at index zero includes the unique empty word. All occurrences of "
                + "Nat.mod mean natural-number remainder; real square roots are nonnegative.")),
            Node("eventLabels", "Labels of adjacent equal pairs", EventLabelsFormula(),
                NameQuote + "Zipping a list with its tail lists adjacent pairs in order. "
                + "Filtering equal pairs and taking their second coordinates records exactly "
                + "the event labels, including both pairs of a triple equal letter.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Admissible", "Cyclic succession of event labels", AdmissibleFormula(),
                NameQuote + "Source position i corresponds to Lean position i-1. Each two "
                + "successive event labels differ by one modulo eight. Empty and singleton "
                + "event lists satisfy List.IsChain. Nonadjacent recurrences are permitted, "
                + "as in the source example (6,4,6,5,4).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The literal word count", CountFormula(),
                NameQuote + "Nat.card counts the subtype of functions satisfying Admissible. "
                + "Words are labeled arrays; no rotation or permutation is identified.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSeries", "Coefficients of the source series", SeriesFormula(),
                FormulaQuote + "PowerSeries has rational coefficients. The constant coefficient "
                + "is zero, and coefficient n is the natural count cast to ℚ for every n ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Barker's two formulas",
                Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                FormulaQuote + "The first clause asserts existence of the coefficient series. "
                + "The second identifies every such series with the rational expression, using "
                + "the inverse in PowerSeries ℚ. The last clause states the radical identity "
                + "over ℝ at every positive natural index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The generating function and radical identity", Disp(ClaimBody()),
                "Prepending a letter partitions words into three states: no event; a first "
                + "event equal to the successor of the first letter; and the remaining words "
                + "with an event. Their counts start at (8,0,0) and transform as "
                + "(U,A,B) ↦ (7U,B,U+8A+6B). Coefficientwise identities give the rational "
                + "series. The total count satisfies the order-three recurrence with "
                + "coefficients 13,-34,-56. The exponential terms with bases 7, 3-√17, "
                + "3+√17 satisfy that recurrence and agree with the counts at indices 1,2,3. "
                + "Uniqueness of recurrence solutions yields the radical formula.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a268943-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula EventLabelsFormula()
    {
        var w = V("w");
        var pair = Seq(Letters(), Times, Letters());
        var filtered = App(Q("List", "filter"),
            Lam("p", pair, Equal(App(Q("Prod", "fst"), V("p")),
                App(Q("Prod", "snd"), V("p")))),
            App(Q("List", "zip"), w, App(Q("List", "tail"), w)));
        return Disp(All("w", App(Named("List"), Letters()),
            Equal(Call("eventLabels", w), App(Q("List", "map"), Q("Prod", "snd"), filtered))));
    }

    private static Formula AdmissibleFormula()
    {
        var relation = Lam("a", Letters(), Lam("b", Letters(),
            Equal(Call("val", V("b")), App(Q("Nat", "mod"),
                Add(Call("val", V("a")), D(1)), D(8)))));
        return Disp(All("n", N(), All("w", Words(V("n")),
            Equal(Call("Admissible", V("w")), App(Q("List", "IsChain"),
                relation, Call("eventLabels", App(Q("List", "ofFn"), V("w"))))))));
    }

    private static Formula CountFormula() => Disp(All("n", N(),
        Equal(Call("count", V("n")), App(Q("Nat", "card"),
            Seq(OpenBrace, V("w"), Colon, Sp, Words(V("n")), Sp, Mid, Sp,
                Call("Admissible", V("w")), CloseBrace)))));

    private static Formula SeriesFormula()
    {
        var constant = Equal(App(Q("PowerSeries", "coeff"), D(0), V("F")), D(0));
        var positive = All("n", N(), Implies(LeOf(D(1), V("n")),
            Equal(App(Q("PowerSeries", "coeff"), V("n"), V("F")),
                Cast(Call("count", V("n")), Rationals()))));
        return Disp(All("F", SeriesType(), Equal(Call("IsSourceSeries", V("F")),
            Parenthesized(And(constant, positive)))));
    }

    private static Formula ClaimBody() => And(
        Some("F", SeriesType(), Call("IsSourceSeries", V("F"))),
        And(All("F", SeriesType(), Implies(Call("IsSourceSeries", V("F")),
                Equal(V("F"), GeneratingFunction()))),
            All("n", N(), Implies(LeOf(D(1), V("n")),
                Equal(Cast(Call("count", V("n")), Reals()), Radical(V("n")))))));

    private static Formula GeneratingFunction()
    {
        var x = Q("PowerSeries", "X");
        var numerator = Multiply(Multiply(D(8), x),
            Parenthesized(Subtract(Subtract(D(1), Multiply(D(5), x)),
                Multiply(D(7), Power(x, D(2))))));
        var denominator = Multiply(Parenthesized(Subtract(D(1), Multiply(D(7), x))),
            Parenthesized(Subtract(Subtract(D(1), Multiply(D(6), x)),
                Multiply(D(8), Power(x, D(2))))));
        return Multiply(numerator, Power(Parenthesized(denominator), new Formula.Negate(D(1))));
    }

    private static Formula Radical(Formula n)
    {
        var s = App(Q("Real", "sqrt"), D(1, 7));
        return new Formula.Fraction(Add(Add(
            Multiply(new Formula.Negate(D(2, 7, 2)), Power(Cast(D(7), Reals()), n)),
            Multiply(Parenthesized(Subtract(D(1, 5, 3), Multiply(D(3, 7), s))),
                Power(Parenthesized(Subtract(D(3), s)), n))),
            Multiply(Power(Parenthesized(Add(D(3), s)), n),
                Parenthesized(Add(D(1, 5, 3), Multiply(D(3, 7), s))))), D(3, 4));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Letters() => Call("Fin", D(8));
    private static Formula Words(Formula n) => Seq(Call("Fin", n), Sp, To, Sp, Letters());
    private static Formula SeriesType() => Call("PowerSeries", Rationals());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Cast(V(name), type), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
