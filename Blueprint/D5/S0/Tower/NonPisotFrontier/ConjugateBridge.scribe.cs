using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class ConjugateBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("betaThirteen");
        var conj = Id("betaThirteenConjugate");
        var p = Id("p");
        var q = Id("q");
        var reals = Id("R");

        var gap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), reals),
            ],
            Equal(
                Subtract(Add(p, Multiply(q, beta)), Add(p, Multiply(q, conj))),
                Multiply(q, Call("sqrt", Num(13)))));

        var expanding = new Formula.Relation(
            Num(1), FormulaRelationOperator.LessThan, new Formula.Absolute(conj));

        var statement = new Formula.Logic(gap, FormulaLogicOperator.And, expanding);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/ConjugateBridge.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A coordinate is the gap between a value and its conjugate, normalised by the "
                + "square root of thirteen.",
            H("Conjugate Bridge"),
            Blocks(
                Paragraph(Text(
                    "The greedy step has the same integer action on coordinates under both "
                        + "embeddings; only the multiplier differs. Since a coordinate equals "
                        + "the normalised gap between the two embeddings, a coordinate sequence "
                        + "is bounded exactly when the conjugate orbit is, and the conjugate "
                        + "multiplier has modulus above one.")),
                Describe.Lean(
                    DescribeId.Create("the-conjugate-bridge-at-the-frontier-base"),
                    DeclarationHandle.Create(declarationPrefix + "conjugate_bridge"),
                    H("The conjugate bridge"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the mechanism behind the frontier claim, not the claim. That "
                            + "the coordinates of the orbit of one actually grow is measured, "
                            + "not proved: their ratio approaches the conjugate modulus to one "
                            + "part in a million by the fiftieth step."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/ExpansionEngine")),
            ]));
    }
}
