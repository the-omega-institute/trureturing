using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicTen;

internal sealed class EnumerationTenValidBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodTenOrbitRepresentatives");

        var statement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("o"),
            orbits,
            new Formula.Logic(
                new Formula.Relation(orbit, FormulaRelationOperator.MemberOf, reps),
                FormulaLogicOperator.Implies,
                Call("tribonacciCodedOrbitValid", orbit)));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidB.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "All forty-two period-ten certificates are valid coded orbits.",
            H("Enumeration Ten Valid B"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against both committed levels before use, "
                        + "and against their rotation classes as sets rather than their counts: "
                        + "it reproduces the fifteen period-eight classes and the twenty-six "
                        + "period-nine classes exactly.")),
                Describe.Lean(
                    DescribeId.Create("all-period-ten-certificates-are-valid"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_ten_representatives_valid"),
                    H("Enumeration Ten Valid B"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The tactic closure is the one the shorter levels use, reused verbatim rather than re-derived."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB")),
            ]));
    }
}
