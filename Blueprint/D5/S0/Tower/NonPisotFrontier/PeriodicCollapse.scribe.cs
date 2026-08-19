using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class PeriodicCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var c = Id("c");
        var y = Id("y");
        var k = Id("k");
        var bound = Id("M");
        var p = Id("p");
        var reals = Id("R");
        var naturals = Id("N");

        var centre = Call("collapseCentre", p, c);
        var iterate = Call("collapseIterate", p, c, k, y);

        var stationary = new Formula.Logic(
            Equal(y, centre),
            FormulaLogicOperator.Implies,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("k"), naturals)],
                Equal(iterate, y)));

        var escaping = new Formula.Logic(
            NotEqual(y, centre),
            FormulaLogicOperator.Implies,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("M"), reals)],
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [new Formula.BoundVariable(FormulaIdentifier.Create("k"), naturals)],
                    new Formula.Relation(
                        bound,
                        FormulaRelationOperator.LessThan,
                        new Formula.Absolute(Subtract(iterate, centre))))));

        var statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("c"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), reals),
            ],
            new Formula.Logic(stationary, FormulaLogicOperator.And, escaping));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/PeriodicCollapse.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A periodic digit block is an affine map with an expanding multiplier, so exactly "
                + "one starting point keeps its conjugate orbit bounded.",
            H("Periodic Collapse"),
            Blocks(
                Paragraph(Text(
                    "Reading a whole period as one step turns it into multiplication by the "
                        + "conjugate raised to the period, followed by subtracting the digits "
                        + "accumulated over that period. That map has one fixed point, and the "
                        + "distance to it is multiplied by the conjugate modulus raised to the "
                        + "period at every block. Since that multiplier exceeds one, the fixed "
                        + "point is the only starting value whose orbit stays bounded; every "
                        + "other one passes every bound.")),
                Describe.Lean(
                    DescribeId.Create("a-periodic-block-collapses-to-one-orbit"),
                    DeclarationHandle.Create(
                        declarationPrefix + "periodic_block_collapses_to_one_orbit"),
                    H("A periodic block collapses to one orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The period is assumed nonzero; that is what makes the multiplier "
                            + "exceed one. Nothing here says which digit sequences actually "
                            + "arise, nor that the orbit of one is among the unbounded ones. "
                            + "It states only the dichotomy that any eventual period forces."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/BetaThirteen")),
            ]));
    }
}
