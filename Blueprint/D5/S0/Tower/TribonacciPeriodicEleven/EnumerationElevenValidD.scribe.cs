using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEleven;

internal sealed class EnumerationElevenValidDDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodElevenOrbitRepresentatives");

        var statement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("o"),
            orbits,
            new Formula.Logic(
                new Formula.Relation(orbit, FormulaRelationOperator.MemberOf, reps),
                FormulaLogicOperator.Implies,
                Call("tribonacciCodedOrbitValid", orbit)));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenValidD.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-eleven Tribonacci certificates, part ValidD.",
            H("Enumeration Eleven ValidD"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against all three committed levels before "
                        + "use, and against their rotation classes as sets rather than their "
                        + "counts: it reproduces the fifteen, twenty-six and forty-two classes "
                        + "exactly.")),
                Describe.Lean(
                    DescribeId.Create("all-period-eleven-certificates-are-valid"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_eleven_representatives_valid"),
                    H("Enumeration Eleven ValidD"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The left and right branch split of the arm minimum was measured for "
                            + "this level: thirty-nine left and thirty-five right. It differs at "
                            + "every level, so the shorter levels' sets are not reusable."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC")),
            ]));
    }
}
