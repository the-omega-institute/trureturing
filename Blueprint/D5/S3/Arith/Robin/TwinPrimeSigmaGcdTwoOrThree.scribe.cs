using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class TwinPrimeSigmaGcdTwoOrThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime sigma-gcd is two or three.", H("A prime sigma-gcd is two or three"),
        Blocks(
            Describe.Lean(DescribeId.Create("a394757-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The exact OEIS conjecture"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second A394757 conjecture asserts that a prime gcd of a twin-prime center and its divisor sum equals two or three. The claim retains both neighboring-prime hypotheses and quantifies over every natural center."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a394757-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal implication"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the divisor sum is even, two divides the prime gcd, which is therefore two. If it is odd, the shared square exclusion gives k=2t^2. Decompose nonzero t as 2^b r with r odd. Then k=2^(2b+1) r^2 and coprime multiplicativity expresses its divisor sum using the geometric sum for 2^(2b+1). The existing geometric-sum formula gives 2^(2b+2)-1, which is divisible by three because 4^(b+1) is congruent to one modulo three. The existing three_center theorem also gives three dividing k, so the prime gcd equals three. This settles preregistration #15004; infinitude remains open."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a394757-sigma-gcd-two-or-three"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimFormula()
    {
        var k = F.Id("k");
        var gcd = Call("gcd", k, Call("sigma", D(1), k));
        var conclusion = Or(Eq(gcd, D(2)), Eq(gcd, D(3)));
        return Disp(Quant(FormulaQuantifier.ForAll, "k",
            Imp(Call("Prime", Sub(k, D(1))),
                Imp(Call("Prime", Add(k, D(1))),
                    Imp(Call("Prime", gcd), conclusion)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Quant(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.BindMany(quantifier,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())], body);
}
