using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotVerdict;

internal sealed class NotEventuallyPeriodicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var p = Id("p");
        var N = Id("N");
        var naturals = Id("N");

        var periodic = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("N"), naturals),
            ],
            new Formula.Logic(
                new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, p),
                FormulaLogicOperator.And,
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [new Formula.BoundVariable(FormulaIdentifier.Create("n"), naturals)],
                    new Formula.Logic(
                        new Formula.Relation(N, FormulaRelationOperator.LessThanOrEqual, n),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call("beta13GreedyDigit", Add(n, p)),
                            Call("beta13GreedyDigit", n))))));

        var statement = new Formula.Not(periodic);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The greedy expansion of one at the frontier base is not eventually periodic.",
            H("Not Eventually Periodic"),
            Blocks(
                Paragraph(Text(
                    "Suppose the digits repeated from some index on. The greedy remainders are "
                        + "confined to the unit interval and the base is expanding, so two "
                        + "sequences driven by those digits could not drift apart: the "
                        + "remainders would repeat with the same period. The reading of a code "
                        + "at the base is injective, so the codes would repeat too.")),
                Paragraph(Text(
                    "Reading those same codes at the conjugate then leaves the conjugate orbit "
                        + "only the values it took before the period closed, of which there are "
                        + "finitely many, so it would be bounded. It is not: from the fourth step "
                        + "onward it is past the escape threshold and the excess is multiplied at "
                        + "every step. The two sides cannot both hold.")),
                Paragraph(Text(
                    "Nothing here is proved for the first time. Every step is a statement landed "
                        + "separately, and the load-bearing one, the exact integer codes "
                        + "and the injectivity of their reading, is not mine. This module "
                        + "is where they meet.")),
                Describe.Lean(
                    DescribeId.Create("the-expansion-is-not-eventually-periodic"),
                    DeclarationHandle.Create(
                        declarationPrefix + "digits_not_eventually_periodic"),
                    H("The expansion is not eventually periodic"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This settles the structural half of the frontier remark for this base. "
                            + "The measured half — that the count of normalised gap types grows "
                            + "with the window, was already carried elsewhere in the "
                            + "tree and is not restated here."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded")),
            ]));
    }
}
