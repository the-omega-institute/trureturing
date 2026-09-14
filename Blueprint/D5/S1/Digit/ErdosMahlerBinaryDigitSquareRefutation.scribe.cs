using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ErdosMahlerBinaryDigitSquareRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/erdos1989mahler");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coprime base-12 square contradicts the reported uniqueness of Mahler's "
        + "nontrivial binary-digit example.",
        H("Mahler's Reported Binary-Digit Square Uniqueness"),
        Blocks(
            Node("binary-base-square", "Binary-digit squares", BinaryBaseSquareFormula(),
                "For natural k and x and a finite set S of natural exponents, "
                    + "BinaryBaseSquare(k,x,S) means that k and x are coprime and the "
                    + "sum of k^i over i in S equals x squared. The finite set may "
                    + "contain zero, as the source's printed base-7 example does.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mahler-reported-uniqueness-claim", "The reported uniqueness suggestion",
                ClaimFormula(),
                "For every base k at least five, root x greater than one, and finite "
                    + "exponent set S, a binary-digit square is asserted to be either "
                    + "the displayed pair (7,20) or a member of the two-digit family. "
                    + "The subtraction x^2 - 1 is natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mahler-reported-uniqueness-refuted", "A base-12 counterexample",
                ResultFormula(),
                "The identity 12^5 + 12^4 + 12^3 + 12^2 + 1 = 521^2 gives a "
                    + "coprime pair outside both alternatives. A second example is "
                    + "8^9 + 8^7 + 8^5 + 8^4 + 8^3 + 8^2 + 8 + 1 = 11677^2. "
                    + "Neither example addresses Mahler's fixed-base finiteness conjecture.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "erdos-1989-mahler-binary-digit-square-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + DeclarationName(id)),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static string DeclarationName(string id) => id switch
    {
        "binary-base-square" => "BinaryBaseSquare",
        "mahler-reported-uniqueness-claim" => "claim",
        "mahler-reported-uniqueness-refuted" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula BinaryBaseSquareFormula()
    {
        var k = F.Id("k");
        var x = F.Id("x");
        var set = F.Id("S");
        var index = F.Id("i");
        var sum = Seq(
            new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, set)),
            Sp, Power(k, index));
        var body = IffFormula(
            Call("BinaryBaseSquare", k, x, set),
            And(Call("Coprime", k, x), Equal(sum, Power(x, D(2)))));
        return Disp(ForAllNaturalsAndFinset(body));
    }

    private static Formula ClaimFormula()
    {
        var k = F.Id("k");
        var x = F.Id("x");
        var set = F.Id("S");
        var alternatives = Or(
            And(Equal(k, D(7)), Equal(x, D(2, 0))),
            Equal(k, Subtract(Power(x, D(2)), D(1))));
        var body = Implies(
            LessThanOrEqual(D(5), k),
            LessThan(D(1), x),
            Call("BinaryBaseSquare", k, x, set),
            alternatives);
        return Disp(IffFormula(F.Id("claim"), ForAllNaturalsAndFinset(body)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula ForAllNaturalsAndFinset(Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("k", Naturals()),
                Bound("x", Naturals()),
                Bound("S", Call("Finset", Naturals())),
            ],
            body);

    private static Formula.BoundVariable Bound(string variable, Formula domain) =>
        new(FormulaIdentifier.Create(variable), domain);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Implies(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
