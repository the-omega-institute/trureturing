using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicTen;

internal sealed class EnumerationTenValidADocument : IScribeDocumentDefinition
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
            "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenValidA.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-ten orbits 01 through 22 are valid coded orbits.",
            H("Enumeration Ten Valid A"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against both committed levels before use, "
                        + "and against their rotation classes as sets rather than their counts: "
                        + "it reproduces the fifteen period-eight classes and the twenty-six "
                        + "period-nine classes exactly.")),
                Describe.Lean(
                    DescribeId.Create("period-ten-orbits-01-22-are-valid"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_ten_orbits_01_02_valid_and_nodup"),
                    H("Enumeration Ten Valid A"),
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
