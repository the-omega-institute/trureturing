using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicNine;

internal sealed class EnumerationNineValidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodNineOrbitRepresentatives");

        var statement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("o"),
            orbits,
            new Formula.Logic(
                new Formula.Relation(orbit, FormulaRelationOperator.MemberOf, reps),
                FormulaLogicOperator.Implies,
                Call("tribonacciCodedOrbitValid", orbit)));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineValid.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "All twenty-six period-nine orbit certificates are valid.",
            H("Enumeration Nine Valid"),
            Blocks(
                Paragraph(Text(
                    "The twenty-six words are the primitive rotation classes among the two "
                        + "hundred forty phase-marked solutions of the period-nine equations. "
                        + "The enumerator was validated against the frozen period-eight data "
                        + "before use: it reproduces one hundred thirty-one phase points and "
                        + "fifteen primitive classes, and those fifteen rotation classes "
                        + "coincide with the committed ones as sets.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-period-nine-representatives-are-valid"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_nine_representatives_valid"),
                    H("Enumeration Nine Valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each certificate carries a low state whose arm lies at or below the "
                            + "champion threshold, so no representative is a strict survivor."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight")),
            ]));
    }
}
