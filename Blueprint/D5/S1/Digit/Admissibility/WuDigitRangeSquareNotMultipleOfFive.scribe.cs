using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class WuDigitRangeSquareNotMultipleOfFiveDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/frohlich2017a254074");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu's A254074 conjecture excludes multiples of five from the specified decimal digit range.",
        H("Digit Extrema Five and Nine Exclude Multiples of Five"),
        Blocks(
            Node(
                "digit-range-five-nine",
                "Decimal digit range from five through nine",
                DigitRangeFormula(),
                "DigitRangeFiveNine(n) means that Mathlib's least-significant-first decimal "
                    + "digit list has List.min? equal to some 5 and List.max? equal to some 9.",
                "DigitRangeFiveNine",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "a254074-result",
                "No term in the digit range is a multiple of five",
                ResultFormula(),
                "If five divides k, the lower digit bound forces its units digit to be 5. "
                    + "Writing k as 10q+5 makes its square congruent to 25 modulo 100. "
                    + "The maximum digit 9 in k makes k at least 59, so the tens digit 2 "
                    + "is present in the square and contradicts its minimum digit 5.",
                "result",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a254074-wu-digit-range-square-not-multiple-of-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula DigitRangeFormula()
    {
        var n = F.Id("n");
        var digits = Call("digits", D(1, 0), n);
        var extrema = And(
            Parenthesized(Equal(Call("min", digits), Call("some", D(5)))),
            Parenthesized(Equal(Call("max", digits), Call("some", D(9)))));
        return Disp(Universal("n", Iff(
            Parenthesized(Call("DigitRangeFiveNine", n)),
            Parenthesized(extrema))));
    }

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        var conclusion = new Formula.Not(Parenthesized(
            new Formula.Relation(D(5), FormulaRelationOperator.Divides, k)));
        var body = Implies(
            Parenthesized(Greater(k, D(0))),
            Implies(
                Parenthesized(Call("DigitRangeFiveNine", k)),
                Implies(
                    Parenthesized(Call("DigitRangeFiveNine", new Formula.Power(k, D(2)))),
                    conclusion)));
        return Disp(Universal("k", body));
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
