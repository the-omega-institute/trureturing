using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class KrizekTriangularSquareSigmaParityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/KrizekTriangularSquareSigmaParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive triangular number is square exactly when its index and value have odd divisor sums.",
        H("Krizek's Triangular-Square Divisor-Sum Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a001108-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The triangular-square divisor-sum characterization"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Arith/sloane2016a001108")),
                Blocks(Paragraph(Text(
                    "The classical divisor-sum parity characterization reduces each odd "
                        + "divisor sum to a square-or-twice-square alternative. A "
                        + "coprime-product split for consecutive integers proves the forward "
                        + "direction, and a twice-square exclusion for triangular numbers "
                        + "proves the reverse direction. At n=0 the triangular number is zero "
                        + "and square, while its divisor sum is even, so positivity excludes "
                        + "that boundary."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a001108-krizek-triangular-square-sigma-parity"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var triangular = Divide(
            Multiply(n, Parenthesized(Add(n, D(1)))),
            D(2));
        var oddSums = And(
            Parenthesized(Call("Odd", SigmaAt(1, n))),
            Parenthesized(Call("Odd", SigmaAt(1, triangular))));
        var characterization = Iff(
            Parenthesized(Call("IsSquare", triangular)),
            Parenthesized(oddSums));
        return Disp(Universal("n", Implies(
            Parenthesized(Greater(n, D(0))),
            Parenthesized(characterization))));
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula SigmaAt(byte index, Formula argument) =>
        new Formula.Apply(new Formula.Subscript(SigmaLower, D(index)), [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Divide(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Slash, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
