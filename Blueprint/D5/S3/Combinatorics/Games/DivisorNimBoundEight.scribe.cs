using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundEightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundEight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive position containing a heap of size eight has "
            + "Sprague–Grundy value at most sixteen.",
        H("The Distinguished Heap Eight"),
        Blocks(
            Node("depth-zero", "Depth zero has value at most five", "eight_depth_zero",
                BoundFormula(0, D(5)),
                "At depth zero, the unique odd heap is different from eight. Its legal "
                    + "removal amounts must divide eight, which has four positive divisors."),
            Node("depth-one", "Depth one has value at most ten", "eight_depth_one",
                BoundFormula(1, D(1, 0)),
                "With a unique minimum, odd removals preserving eight have value at most "
                    + "five. Replacing eight leaves an odd heap at most seven; remainders "
                    + "at most five give value at most six, and the remainder seven also "
                    + "gives value at most six because two of its removal amounts give "
                    + "zero. There are at most three exceptional even removals. With "
                    + "several minimum heaps, the ordinary recurrence gives value at most nine."),
            Node("depth-two", "Depth two has value at most fourteen", "eight_depth_two",
                BoundFormula(2, D(1, 4)),
                "Lower-depth followers have value at most eleven: the unchanged-eight "
                    + "bounds are five and ten, and the changed-eight bounds are eight "
                    + "and eleven. At most two exceptional removal values give the bound fourteen."),
            Node("heap-eight", "Every position containing eight has value at most sixteen",
                "eight_bound", UniversalFormula(),
                "The position depth is at most three. At depth three the preceding "
                    + "bounds give fourteen for every ordinary follower, and the unique "
                    + "possible exceptional removal gives sixteen.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula BoundFormula(byte k, Formula bound)
    {
        var p = F.Id("P");
        return Disp(All("P", Call("Multiset", Nat()), Imp(And(Call("Positive", p),
            And(Call("HasDepth", p, D(k)), Call("mem", D(8), p))),
            Le(Call("grundy", p), bound))));
    }
    private static Formula UniversalFormula()
    {
        var p = F.Id("P");
        return Disp(All("P", Call("Multiset", Nat()), Imp(And(Call("Positive", p),
            Call("mem", D(8), p)), Le(Call("grundy", p), D(1, 6)))));
    }
}
