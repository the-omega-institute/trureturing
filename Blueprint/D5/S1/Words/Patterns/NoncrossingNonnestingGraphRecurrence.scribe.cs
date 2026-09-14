using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class NoncrossingNonnestingGraphRecurrenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/barker2019a326244");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's recurrence counts labeled simple graphs whose edges neither cross nor nest.",
        H("Crossing- and Nesting-Free Labeled Graphs"),
        Blocks(
            Paragraph(Text(
                "Vertices are linearly ordered by Fin(n). An edge is an ordered pair whose "
                + "first endpoint is smaller than its second endpoint. The count uses literal "
                + "finite sets of such ordered pairs.")),
            Node("Crossing", "Crossing edges", CrossingFormula(),
                "Two ordered pairs cross exactly when their four endpoints occur in one of the "
                + "two alternating orders stated in the OEIS entry.",
                DescribeRole.Definition),
            Node("Nesting", "Nesting edges", NestingFormula(),
                "The endpoints of one edge lie strictly between the endpoints of the other, "
                + "with both edges increasing.",
                DescribeRole.Definition),
            Node("IsAvoiding", "Graphs avoiding both edge patterns", AvoidingFormula(),
                "Every edge is increasing, and every ordered pair of edges avoids both crossing "
                + "and nesting. Repeated choices of the same edge are included in the universal "
                + "condition and satisfy it automatically.",
                DescribeRole.Definition),
            Node("a", "The A326244 counting function", CountingFormula(),
                "The value a(n) is the cardinality of the filter of avoiding edge sets inside "
                + "the finite universe of all edge sets on Fin(n).",
                DescribeRole.Definition),
            Node("barker_a326244", "Barker's third-order recurrence", RecurrenceFormula(),
                "Removing the greatest vertex identifies every avoiding graph on n+1 vertices "
                + "with an avoiding graph G on n vertices and a subset of its allowed vertices. "
                + "The new allowed-set size is r+1, 2, or 1 according as the chosen subset is "
                + "empty, a singleton, or has at least two members. Three weighted counts obey "
                + "first-order identities; eliminating the two auxiliary moments gives the "
                + "displayed recurrence for every n greater than two.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a326244-noncrossing-nonnesting-graph-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a326244-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CrossingFormula() => PatternFormula("Crossing", crossing: true);

    private static Formula NestingFormula() => PatternFormula("Nesting", crossing: false);

    private static Formula PatternFormula(string name, bool crossing)
    {
        var n = F.Id("n");
        var e = F.Id("e");
        var f = F.Id("f");
        var first = crossing
            ? And(LtOf(Fst(e), Fst(f)), And(LtOf(Fst(f), Snd(e)), LtOf(Snd(e), Snd(f))))
            : And(LtOf(Fst(e), Fst(f)), And(LtOf(Fst(f), Snd(f)), LtOf(Snd(f), Snd(e))));
        var second = crossing
            ? And(LtOf(Fst(f), Fst(e)), And(LtOf(Fst(e), Snd(f)), LtOf(Snd(f), Snd(e))))
            : And(LtOf(Fst(f), Fst(e)), And(LtOf(Fst(e), Snd(e)), LtOf(Snd(e), Snd(f))));
        var equivalence = IffOf(Call(name, e, f),
            Parenthesized(Or(Parenthesized(first), Parenthesized(second))));
        return Disp(ForAll("n", Naturals(),
            ForAllMany([("e", EdgeType(n)), ("f", EdgeType(n))], equivalence)));
    }

    private static Formula AvoidingFormula()
    {
        var n = F.Id("n");
        var edges = F.Id("E");
        var e = F.Id("e");
        var f = F.Id("f");
        var increasing = ForAll("e", edges, LtOf(Fst(e), Snd(e)));
        var patterns = ForAll("e", edges, ForAll("f", edges,
            And(Not(Call("Crossing", e, f)), Not(Call("Nesting", e, f)))));
        return Disp(ForAll("n", Naturals(), ForAll("E", Finset(EdgeType(n)),
            IffOf(Call("IsAvoiding", edges), Parenthesized(And(increasing, patterns))))));
    }

    private static Formula CountingFormula()
    {
        var n = F.Id("n");
        var edges = F.Id("E");
        var predicate = Parenthesized(Seq(edges, Sp, Mapsto, Sp, Call("IsAvoiding", edges)));
        var universe = Call("univ", Finset(EdgeType(n)));
        return Disp(ForAll("n", Naturals(),
            EqOf(Call("a", n), Call("card", Call("filter", predicate, universe)))));
    }

    private static Formula RecurrenceFormula()
    {
        var n = F.Id("n");
        Formula cast(Formula value) => Call("Int", value);
        var right = Add(
            Subtract(Multiply(D(6), cast(Call("a", Subtract(n, D(1))))),
                Multiply(D(8), cast(Call("a", Subtract(n, D(2)))))),
            Multiply(D(4), cast(Call("a", Subtract(n, D(3))))));
        return Disp(ForAll("n", Naturals(), Implies(LtOf(D(2), n),
            EqOf(cast(Call("a", n)), right))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula EdgeType(Formula n) =>
        Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", n));
    private static Formula Finset(Formula type) => Call("Finset", Parenthesized(type));
    private static Formula Fst(Formula value) => Call("fst", value);
    private static Formula Snd(Formula value) => Call("snd", value);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany((string Name, Formula Domain)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))], body);
    private static Formula EqOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LtOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
