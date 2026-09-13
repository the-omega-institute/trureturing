using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SelfReferentialDoublingFirstOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/alkan2020a335901");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alkan's self-referential doubling recurrence has first-occurrence positions A117261.",
        H("First Occurrences in the Self-Referential Doubling Recurrence"),
        Blocks(
            Paragraph(Text(
                "The sequence a is totalized at index zero by a sentinel value one, while "
                + "the source recurrence starts at index one. For every natural n at least "
                + "two, the next value is twice the value at the floor of (n-1) divided by "
                + "the preceding value.")),
            Paragraph(Text(
                "The auxiliary sequence T is A117261 in recurrence form. The theorem states "
                + "both the value at every block start and the least positive index carrying "
                + "the corresponding power of two.")),
            Node("a", "The A335901 recurrence", AFormula(),
                "The displayed clauses give a(1)=1 and the source recurrence for every "
                + "natural n with n at least two. The sentinel at a(0) only totalizes the "
                + "recursive definition and is not part of the source sequence.",
                DescribeRole.Definition),
            Node("T", "The A117261 threshold sequence", TFormula(),
                "This is A117261 with T(0)=1 and T(r+1)=2^r times T(r) plus one for every "
                + "natural r.",
                DescribeRole.Definition),
            Node("alkan_a335901", "Least indices for powers of two", TheoremFormula(),
                "For every natural r, the value at T(r) is 2^r. Every natural k with "
                + "1 <= k and a(k)=2^r is at least T(r), so T(r) is the least positive "
                + "index carrying that value.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a335901-self-referential-doubling-first-occurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a335901-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var previous = new Formula.Binary(n, FormulaBinaryOperator.Subtract, D(1));
        var quotient = new Formula.Fraction(previous, Call("a", previous));
        var recurrence = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(
                new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    Call("a", n),
                    FormulaRelationOperator.Equal,
                    new Formula.Binary(
                        D(2),
                        FormulaBinaryOperator.Multiply,
                        Call("a", new Formula.Floor(quotient))))));
        return Disp(new Formula.Logic(
            new Formula.Relation(Call("a", D(1)), FormulaRelationOperator.Equal, D(1)),
            FormulaLogicOperator.And,
            recurrence));
    }

    private static Formula TFormula()
    {
        var r = F.Id("r");
        var step = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("r"),
            Naturals(),
            new Formula.Relation(
                Call("T", new Formula.Binary(r, FormulaBinaryOperator.Add, D(1))),
                FormulaRelationOperator.Equal,
                new Formula.Binary(
                    new Formula.Binary(
                        new Formula.Power(D(2), r),
                        FormulaBinaryOperator.Multiply,
                        Call("T", r)),
                    FormulaBinaryOperator.Add,
                    D(1))));
        return Disp(new Formula.Logic(
            new Formula.Relation(Call("T", D(0)), FormulaRelationOperator.Equal, D(1)),
            FormulaLogicOperator.And,
            step));
    }

    private static Formula TheoremFormula()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var power = new Formula.Power(D(2), r);
        var minimality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Naturals(),
            new Formula.Logic(
                new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, k),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    new Formula.Relation(Call("a", k), FormulaRelationOperator.Equal, power),
                    FormulaLogicOperator.Implies,
                    new Formula.Relation(Call("T", r), FormulaRelationOperator.LessThanOrEqual, k))));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("r"),
            Naturals(),
            new Formula.Logic(
                new Formula.Relation(Call("a", Call("T", r)), FormulaRelationOperator.Equal, power),
                FormulaLogicOperator.And,
                minimality)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
