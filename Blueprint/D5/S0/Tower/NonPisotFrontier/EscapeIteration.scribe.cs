using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class EscapeIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x = Id("x");
        var d = Id("d");
        var conj = Id("betaThirteenConjugate");
        var thr = Id("escapeThreshold");
        var reals = Id("R");

        var image = new Formula.Absolute(Subtract(Multiply(conj, x), d));

        var growth = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), reals),
            ],
            new Formula.Logic(
                new Formula.Relation(thr, FormulaRelationOperator.LessThan,
                    new Formula.Absolute(x)),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    Add(thr, Multiply(new Formula.Absolute(conj),
                        Subtract(new Formula.Absolute(x), thr))),
                    FormulaRelationOperator.LessThanOrEqual,
                    image)));

        var expanding = new Formula.Relation(
            Num(1), FormulaRelationOperator.LessThan, new Formula.Absolute(conj));

        var statement = new Formula.Logic(expanding, FormulaLogicOperator.And, growth);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/EscapeIteration.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Past the threshold, one step multiplies the excess above it by the conjugate "
                + "modulus.",
            H("Escape Iteration"),
            Blocks(
                Paragraph(Text(
                    "Naming the excess above the threshold turns the escape into a single "
                        + "multiplicative statement. The multiplier identity is the threshold "
                        + "identity rearranged, so no new arithmetic about the base is needed: "
                        + "the modulus carries the threshold to the threshold plus two.")),
                Describe.Lean(
                    DescribeId.Create("the-escape-iterates"),
                    DeclarationHandle.Create(declarationPrefix + "escape_iterates"),
                    H("The escape iterates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The image stays past the threshold, so the step applies again. With "
                            + "the witness already established four steps along the orbit, the "
                            + "conjugate coordinates cannot remain bounded."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/EscapeThreshold")),
            ]));
    }
}
