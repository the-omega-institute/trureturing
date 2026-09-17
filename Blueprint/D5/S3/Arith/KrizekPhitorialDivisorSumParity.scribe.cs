using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class KrizekPhitorialDivisorSumParityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/KrizekPhitorialDivisorSumParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/krizek2017a280258");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The divisor sum of phitorials is odd exactly away from twice a square.",
        H("Krizek's Phitorial Divisor-Sum Parity Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a280258-phitorial"),
                DeclarationHandle.Create(Prefix + "phitorial"),
                H("The product of totatives"),
                StatementSource.FromAuthor(PhitorialFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The product ranges over all k in the inclusive interval from one to m "
                        + "that are coprime to m. For m=1 the value is one. For m at least "
                        + "two, the endpoint m is removed because gcd(m,m) is not one, so "
                        + "the inclusive and half-open readings agree there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a280258-divisor-sum"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The sum of phitorials over divisors"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, the value a(n) is the sum of phitorial(d) over "
                        + "the positive divisors d of n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a280258-printed-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The printed parity claim"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The domain is positive n. The single biconditional says that a(n) is "
                        + "odd precisely when n is not twice a square, combining the two "
                        + "parity classes printed in the source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a280258-parity-characterization"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The phitorial divisor-sum parity characterization"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A phitorial is odd exactly at one and at even inputs. The number of "
                        + "divisors of a positive integer is odd exactly for a square, while "
                        + "halving the even divisors of 2m gives a bijection with the divisors "
                        + "of m. These facts determine the parity of the divisor sum."))),
                DescribeRole.Theorem))));

    private static Formula PhitorialFormula()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var interval = Seq(OpenBracket, D(1), Comma, Sp, m, CloseBracket);
        var condition = Seq(k, Sp, InMacro, Sp, interval, Comma, Sp,
            Call("Coprime", k, m));
        var product = Seq(new Formula.Subscript(Prod, condition), Sp, k);
        return Disp(Universal("m", Equal(Call("phitorial", m), product)));
    }

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var index = Seq(d, Sp, InMacro, Sp, Call("divisors", n));
        var sum = Seq(new Formula.Subscript(Sum, index), Sp, Call("phitorial", d));
        return Disp(Universal("n", Equal(Call("a", n), sum)));
    }

    private static Formula ClaimFormula() =>
        Disp(Iff(F.Id("claim"), ClaimBody()));

    private static Formula ResultFormula() => Disp(ClaimBody());

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var positive = Greater(n, D(0));
        var parity = Iff(
            Parenthesized(Call("Odd", Call("a", n))),
            Parenthesized(Not(TwiceSquare(n))));
        return Universal("n", Implies(Parenthesized(positive), Parenthesized(parity)));
    }

    private static Formula TwiceSquare(Formula n)
    {
        var k = F.Id("k");
        var equation = Equal(n, Multiply(D(2), Power(k, D(2))));
        return Existential("k", equation);
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Existential(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Not(Formula value) =>
        Seq(Neg, Sp, Parenthesized(value));

    private static Formula Power(Formula basis, Formula exponent) =>
        Seq(Grp(basis), Caret, Grp(exponent));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
