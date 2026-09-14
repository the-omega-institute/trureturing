using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class IsraelLaguerreFourParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/IsraelLaguerreFourParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/sloane2018a160627");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laguerre(n,4) has odd reduced numerator and denominator for every natural n.",
        H("Israel's Laguerre Polynomial Parity Conjectures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a160627-l"),
                DeclarationHandle.Create(Prefix + "L"),
                H("The Laguerre polynomial at four"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The finite binomial sum is the classical Laguerre polynomial evaluated "
                        + "at x=4. The operator binomial denotes Nat.choose, and the slash "
                        + "denotes rational division after the natural factorial is cast to Q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a160627-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Odd numerator and denominator"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every nonconstant summand has positive 2-adic valuation because the "
                        + "valuation of k factorial is less than k. The ultrametric sum law "
                        + "therefore gives valuation zero for L(n). Reducedness then excludes "
                        + "a factor of two from both num(L(n)) and den(L(n))."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a160627-israel-laguerre-four-parity"),
                    ResolutionKind.Proved)))));

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var boundedSum = Seq(
            Sum, Underscore, Grp(k, Sp, Eq, Sp, D(0)), Caret, Grp(n));
        var choose = Call("binomial", n, k);
        var negativeFourPower = new Formula.Power(
            Parenthesized(Seq(Minus, D(4))), k);
        var numerator = new Formula.Binary(
            choose, FormulaBinaryOperator.Multiply, negativeFourPower);
        var summand = Seq(numerator, Sp, Slash, Sp, Factorial(k));
        return Universal(n, Equal(Call("L", n), Seq(boundedSum, Sp, summand)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var value = Call("L", n);
        var parity = new Formula.Logic(
            Parenthesized(Call("Odd", Call("num", value))),
            FormulaLogicOperator.And,
            Parenthesized(Call("Odd", Call("den", value))));
        return Universal(n, parity);
    }

    private static Formula Universal(Formula variable, Formula body) => Disp(
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            body));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Factorial(Formula value) => Seq(value, Bang);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
