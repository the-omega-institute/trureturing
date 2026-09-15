using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class SquarePrependOneAppendTwentyFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/wu2014a249621");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu's A249621 conjecture for squares preserved by a decimal prefix and suffix.",
        H("Squares Preserved by a Decimal Prefix and Suffix"),
        Blocks(
            Paragraph(Text(
                "For a natural number x, the base-ten digits are written by Nat.digits 10 x. "
                + "Prepending 1 and appending 25 produces the value "
                + "10^(length(digits(10,x)) + 2) + 100*x + 25.")),
            Node("IsMember", "A249621 membership", IsMemberFormula(),
                "Membership requires x to be a square and the base-ten concatenation 1||x||25 "
                + "to be a square as well.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("wu_a249621", "Wu's terminal-digit conjecture", TheoremFormula(),
                "Every member x with x at least 1 has final two decimal digits 00 or 56. "
                + "The proof reduces the second square root modulo 5, then classifies the "
                + "resulting square congruence modulo 400.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a249621-square-prepend-one-append-twenty-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a249621-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula IsMemberFormula()
    {
        var x = F.Id("x");
        var square = new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create("z"), Naturals(),
            Equal(x, new Formula.Power(F.Id("z"), D(2))));
        var appended = new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create("y"), Naturals(),
            Equal(new Formula.Power(F.Id("y"), D(2)),
                Add(Add(new Formula.Power(D(1, 0), Add(DigitLength(x), D(2))),
                    Multiply(D(1, 0, 0), x)), D(2, 5))));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("x"), Naturals(),
            new Formula.Logic(
                Call("IsMember", x), FormulaLogicOperator.Iff,
                Parenthesized(new Formula.Logic(square, FormulaLogicOperator.And, appended)))));
    }

    private static Formula TheoremFormula()
    {
        var x = F.Id("x");
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("x"), Naturals(),
            new Formula.Logic(
                new Formula.Relation(x, FormulaRelationOperator.GreaterThan, D(0)),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    Call("IsMember", x), FormulaLogicOperator.Implies,
                    new Formula.Logic(
                        new Formula.Relation(new Formula.Modulo(x, D(1, 0, 0)),
                            FormulaRelationOperator.Equal, D(0)),
                        FormulaLogicOperator.Or,
                        new Formula.Relation(new Formula.Modulo(x, D(1, 0, 0)),
                            FormulaRelationOperator.Equal, D(5, 6)))))));
    }

    private static Formula Naturals() => F.Id("Nat");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula DigitLength(Formula x) => Call("length", Call("digits", D(1, 0), x));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
