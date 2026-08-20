using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class BetaThirteenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("betaThirteen");
        var conj = Id("betaThirteenConjugate");

        Formula Quadratic(Formula x) =>
            Equal(new Formula.Power(x, Num(2)), Add(x, Num(3)));

        var statement = new Formula.Logic(
            new Formula.Logic(
                Quadratic(beta),
                FormulaLogicOperator.And,
                new Formula.Relation(Num(2), FormulaRelationOperator.LessThan, beta)),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Quadratic(conj),
                FormulaLogicOperator.And,
                new Formula.Relation(Num(1), FormulaRelationOperator.LessThan,
                    new Formula.Absolute(conj))));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/BetaThirteen.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The frontier base has a conjugate of modulus above one, so it lies outside the "
                + "Pisot region and outside the d-bonacci family.",
            H("Beta Thirteen"),
            Blocks(
                Paragraph(Text(
                    "This is the precondition of the frontier claim, not the claim itself. A "
                        + "Pisot base has every conjugate of modulus below one; this base does "
                        + "not, and it also exceeds two, whereas every d-bonacci Perron root "
                        + "lies below two. The two facts together place it outside both "
                        + "families that the tower machinery covers.")),
                Describe.Lean(
                    DescribeId.Create("the-frontier-base-lies-outside-the-pisot-region"),
                    DeclarationHandle.Create(
                        declarationPrefix + "betaThirteen_is_outside_the_pisot_region"),
                    H("The frontier base lies outside the Pisot region"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Stated concretely as a modulus bound rather than through a Pisot "
                            + "predicate, because the pinned Mathlib has no such predicate. The "
                            + "linear growth of the gap alphabet at this base is measured but "
                            + "not proved here."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacci/PerronRoot")),
            ]));
    }
}
