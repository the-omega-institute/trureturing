using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class ChampionMidBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var naturals = Id("N");
        var indexed = Call("championMid", d);
        var general = Call("championMidCoordinate", Call("dbonacciPerronRoot", d));

        var pointwise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("d"), naturals)],
            Equal(indexed, general));

        var limit = Call("Tendsto", Id("championMid"), Id("atTop"),
            Call("nhds", new Formula.Fraction(Num(1), Num(3))));

        var statement = new Formula.Logic(pointwise, FormulaLogicOperator.And, limit);

        const string declarationPrefix =
            "D5/S0/Tower/DBonacciGeneral/ChampionMidBridge.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The indexed middle coordinate is the general one at the Perron root, so the limit "
                + "carries across.",
            H("Champion Middle Bridge"),
            Blocks(
                Paragraph(Text(
                    "One value was written twice: once indexed by the arity and once as a "
                        + "function of the base, twenty-three minutes apart. The indexed one was "
                        + "already frozen when the general one appeared, so the link could not "
                        + "be made where it belonged, in the module that generalised it.")),
                Paragraph(Text(
                    "Stating the identity is what remains, and it earns its place rather than "
                        + "only tidying: the limit was proved for the general form, and this "
                        + "carries it to the indexed form, which had no limit statement of its "
                        + "own.")),
                Describe.Lean(
                    DescribeId.Create("the-two-middle-coordinates-are-one"),
                    DeclarationHandle.Create(
                        declarationPrefix + "the_two_middle_coordinates_are_one"),
                    H("The two middle coordinates are one"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The pattern that would have avoided this is one directory over: the "
                            + "base itself is a short name whose body is the single source it "
                            + "delegates to, so the two can never drift. When a general form "
                            + "arrives for something already in the tree, it owes the specific "
                            + "form that link, and the debt falls due in the same change."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/ChampionLimit")),
            ]));
    }
}
