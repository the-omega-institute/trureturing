using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class TwinPrimeSigmaGcdThreeTwiceSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sigma-gcd of three forces twice a square.", H("A sigma-gcd of three forces twice a square"),
        Blocks(
            Describe.Lean(DescribeId.Create("odd-sigma-twice-square"),
                DeclarationHandle.Create(Prefix + "twice_square_of_odd_sigma"),
                H("The square alternative is excluded above four"),
                StatementSource.FromAuthor(HelperFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k greater than four, primality of k-1 excludes a square center. "
                    + "An odd divisor sum therefore forces k to be twice a square. "
                    + "The two-or-three theorem consumes this public helper."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a394399-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The exact OEIS conjecture"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact A394399 conjecture asserts that every twin-prime center with sigma-gcd three is twice a square. The implication holds for all natural numbers with truncated natural subtraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a394399-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal implication"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing even_center theorem forces two to divide the center. A gcd of three prevents two from dividing its divisor sum, so the sum is odd. The reused square-or-twice-square parity criterion supplies two alternatives. A square center factors k-1 as (s-1)(s+1); primality forces the boundary k=4, where sigma(4)=7 and the gcd is one. The remaining alternative is twice a square. This settles preregistration #15003; it proves no infinitude assertion."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a394399-twin-prime-sigma-gcd-three"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimFormula()
    {
        var k = F.Id("k");
        var gcd = Call("gcd", k, Call("sigma", D(1), k));
        var conclusion = TwiceSquare(k);
        return Disp(Quant(FormulaQuantifier.ForAll, "k",
            Imp(Call("Prime", Sub(k, D(1))),
                Imp(Call("Prime", Add(k, D(1))),
                    Imp(Eq(gcd, D(3)), conclusion)))));
    }

    private static Formula HelperFormula()
    {
        var k = F.Id("k");
        return Disp(Quant(FormulaQuantifier.ForAll, "k",
            Imp(Lt(D(4), k), Imp(Call("Prime", Sub(k, D(1))),
                Imp(Call("Odd", Call("sigma", D(1), k)), TwiceSquare(k))))));
    }

    private static Formula TwiceSquare(Formula k) =>
        Quant(FormulaQuantifier.Exists, "m",
            Eq(k, Mul(D(2), new Formula.Power(F.Id("m"), D(2)))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Quant(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.BindMany(quantifier,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())], body);
}
