using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciSurvivors;

internal sealed class DBonacciPermanentSurvivorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Empty(Formula set) => Equal(set, Id("emptySet"));

        Formula Nonempty(Formula states, Formula set) => new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"),
            states,
            new Formula.Relation(Id("s"), FormulaRelationOperator.MemberOf, set));

        var fourStates = Call("State", FormulaDsl.D(4));
        var fiveStates = Call("State", FormulaDsl.D(5));
        var fourStrictPermanent = Id("dbonacciFourStrictPermanentSet");
        var fiveStrictPermanent = Id("dbonacciFiveStrictPermanentSet");
        var fourClosedPermanent = Id("dbonacciFourClosedPermanentSet");
        var fiveClosedPermanent = Id("dbonacciFiveClosedPermanentSet");

        const string declarationPrefix =
            "D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Strict four- and five-bonacci permanent survival is empty, while each closed "
                + "threshold retains its champion period-two carrier.",
            H("D-Bonacci Permanent Survivors"),
            Blocks(
                Paragraph(Text(
                    "The typed d-bonacci alphabet gives four gap kinds at order four and five "
                        + "gap kinds at order five. A uniform transition sends a zero label to "
                        + "the top gap and splits every positive label into a top or predecessor "
                        + "branch. Two order-specific barrier inequalities force a hypothetical "
                        + "strict permanent orbit onto the expanding top-gap two-cycle. The "
                        + "inverse-square distance estimate then forces its boundary point, which "
                        + "the strict domain excludes.")),
                Describe.Lean(
                    DescribeId.Create("strict-four-bonacci-permanent-set-is-empty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "dbonacci_four_strict_permanent_set_eq_empty"),
                    H("The strict four-bonacci permanent set is empty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Empty(fourStrictPermanent))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is an all-depth intersection statement: no four-gap state survives "
                            + "every finite backward depth. It does not assert that the finite "
                            + "survivor set at depth 60 is empty."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("strict-five-bonacci-permanent-set-is-empty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "dbonacci_five_strict_permanent_set_eq_empty"),
                    H("The strict five-bonacci permanent set is empty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Empty(fiveStrictPermanent))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is likewise an all-depth intersection statement, not a proof that "
                            + "the finite depth-60 survivor set is empty."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("closed-four-bonacci-permanent-set-is-nonempty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "dbonacci_four_closed_permanent_set_nonempty"),
                    H("The closed four-bonacci permanent set is nonempty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        Nonempty(fourStates, fourClosedPermanent))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The top and predecessor champion states form a closed period-two orbit. "
                            + "This proves a lower bound for the closed permanent set and is not "
                            + "used to prove strict emptiness."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("closed-five-bonacci-permanent-set-is-nonempty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "dbonacci_five_closed_permanent_set_nonempty"),
                    H("The closed five-bonacci permanent set is nonempty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        Nonempty(fiveStates, fiveClosedPermanent))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The five-bonacci champion states give the analogous closed period-two "
                            + "carrier. Strict and closed thresholds remain separate definitions "
                            + "and separate theorems."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacci/OrbitAlgebra")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacci/ChampionOrbit")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit")),
            ]));
    }
}
