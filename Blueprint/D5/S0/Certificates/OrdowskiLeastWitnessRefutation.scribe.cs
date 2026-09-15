using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class OrdowskiLeastWitnessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/OrdowskiLeastWitnessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/ordowski2018a126762");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed exponent-shift conjecture for OEIS A126762 fails at n = 363.",
        H("The OEIS A126762 Least-Witness Exponent-Shift Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a126762-first-congruence"),
                DeclarationHandle.Create(Prefix + "firstCongruence"),
                H("The defining congruence for A126762"),
                StatementSource.FromAuthor(FirstCongruenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural numbers n and k, the defining condition requires k to be "
                        + "strictly greater than n and the remainder of n to the power k "
                        + "modulo k to equal the remainder of n modulo k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a126762-second-congruence"),
                DeclarationHandle.Create(Prefix + "secondCongruence"),
                H("The proposed exponent-shift congruence"),
                StatementSource.FromAuthor(SecondCongruenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The proposed condition keeps k strictly greater than n, changes the "
                        + "exponent to k minus one, and requires remainder one modulo k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a126762-ordowski-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Ordowski's least-witness conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive n, the printed conjecture says that any k least "
                        + "among the witnesses of the defining condition is also least "
                        + "among the witnesses of the exponent-shift condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a126762-ordowski-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 363"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At n = 363, the remainders of 363 to the powers 364, 365, and "
                            + "366 modulo 364, 365, and 366 are 1, 333, and 363. Thus "
                            + "366 is the least witness of the defining condition.")),
                    Paragraph(Text(
                        "The remainder of 363 to the power 365 modulo 366 is 123 rather "
                            + "than 1, so 366 is not a witness of the proposed condition. "
                            + "This refutes only the printed conjecture. It makes no claim "
                            + "about a corrected sequence or the second least witness 367."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a126762-least-witness-exponent-shift-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula FirstCongruenceFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        return Universal(Iff(
            Call("firstCongruence", n, k),
            Parenthesized(And(
                Relation(n, FormulaRelationOperator.LessThan, k),
                Relation(
                    new Formula.Modulo(new Formula.Power(n, k), k),
                    FormulaRelationOperator.Equal,
                    new Formula.Modulo(n, k))))));
    }

    private static Formula SecondCongruenceFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        return Universal(Iff(
            Call("secondCongruence", n, k),
            Parenthesized(And(
                Relation(n, FormulaRelationOperator.LessThan, k),
                Relation(
                    new Formula.Modulo(
                        new Formula.Power(
                            n,
                            new Formula.Binary(k, FormulaBinaryOperator.Subtract, D(1))),
                        k),
                    FormulaRelationOperator.Equal,
                    new Formula.Modulo(D(1), k))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        var firstWitnesses = SetOf(j, Call("firstCongruence", n, j));
        var secondWitnesses = SetOf(j, Call("secondCongruence", n, j));
        var body = Implies(
            Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            Implies(
                Call("IsLeast", firstWitnesses, k),
                Call("IsLeast", secondWitnesses, k)));
        return Universal(body);
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(Formula body) =>
        Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Naturals()),
            ],
            body));

    private static Formula SetOf(Formula variable, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
