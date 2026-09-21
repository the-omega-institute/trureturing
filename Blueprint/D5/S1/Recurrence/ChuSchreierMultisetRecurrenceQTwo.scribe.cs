using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class ChuSchreierMultisetRecurrenceQTwoDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/chu2026schreiermultisets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first q=2 Schreier-multiset counting sequence obeys its conjectured recurrence.",
        H("The First Schreier-Multiset Recurrence for q = 2"),
        Blocks(
            Node("ground-multiset", "The ground multiset", "ground",
                GroundFormula(),
                "For each natural n, the interval from one through n-1 contributes two "
                    + "copies of every entry, and one distinguished copy of n is added. "
                    + "This is the s=2 ground multiset in the page-19 definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissible-submultisets", "The admissible sub-multisets", "A",
                AFormula(),
                "The powerset operation enumerates sub-multisets with multiplicity, so "
                    + "toFinset removes repeated enumerations and yields the finite set of "
                    + "sub-multisets of ground(n). The filter requires n to occur and the "
                    + "multiset cardinality |F| to be at most twice min F. In Lean, min F "
                    + "is F.toFinset.min' with the occurrence of n supplying nonemptiness.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("counting-sequence", "The counting sequence", "a",
                ACountFormula(),
                "The term a(n) is the cardinality of the finite set A(n), hence it counts "
                    + "distinct admissible sub-multisets rather than their repeated "
                    + "occurrences in Multiset.powerset.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjectured-recurrence", "The conjectured recurrence", "claim",
                ClaimFormula(),
                "The source does not print a starting index. The statement begins at four, "
                    + "the least index for which n, n-1, n-2, and n-3 all lie in the "
                    + "sequence indexed from one. Subtraction is truncated natural-number "
                    + "subtraction, and under 4<=n it agrees with the displayed indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("recurrence-proof", "The recurrence", "result",
                ResultFormula(),
                "Admissible sub-multisets are put in bijection with the disjoint union of "
                    + "ordered compositions of 2n-2 and 2n-1 whose parts are 2, 3, or 4. "
                    + "Removing the first part gives the composition recurrence with shifts "
                    + "2, 3, and 4; applying it to the four adjacent counting terms gives "
                    + "the stated recurrence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula GroundFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        Formula interval = Call("Icc", D(1), Subtract(n, D(1)));
        Formula repeated = Call("bind", Call("val", interval),
            LambdaTerm("i", Call("replicate", D(2), i)));
        return Disp(ForAll("n", Naturals(),
            Equal(Call("ground", n), Add(repeated, Call("singleton", n)))));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), multiset = F.Id("F");
        Formula candidates = Call("toFinset", Call("powerset", Call("ground", n)));
        Formula condition = And(Member(n, multiset),
            AtMost(Cardinality(multiset), Multiply(D(2), Minimum(multiset))));
        return Disp(ForAll("n", Naturals(), Equal(Call("A", n),
            Call("filter", LambdaTerm("F", condition), candidates))));
    }

    private static Formula ACountFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Naturals(),
            Equal(Call("a", n), Cardinality(Call("A", n)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula recurrence = Equal(Call("a", n),
            Add(Add(Call("a", Subtract(n, D(1))),
                Multiply(D(2), Call("a", Subtract(n, D(2))))),
                Call("a", Subtract(n, D(3)))));
        Formula body = ForAll("n", Naturals(),
            Implies(AtMost(D(4), n), recurrence));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Cardinality(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Minimum(Formula value) => Seq(Min, Sp, value);

    private static Formula LambdaTerm(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Sp, Mapsto, Sp, body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), domain, body);
}
