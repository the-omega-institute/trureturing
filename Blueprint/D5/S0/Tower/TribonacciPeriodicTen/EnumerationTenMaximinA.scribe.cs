using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicTen;

internal sealed class EnumerationTenMaximinADocument : IScribeDocumentDefinition
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
                new Formula.Relation(
                    Call("tribonacciPeriodicStateArm",
                        Call("decodeTribonacciState", Call("lowState", orbit))),
                    FormulaRelationOperator.LessThanOrEqual,
                    Call("championValue", Id("t")))));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinA.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-ten orbits 01 through 14 have a low arm below the champion.",
            H("Enumeration Ten Maximin A"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against both committed levels before use, "
                        + "and against their rotation classes as sets rather than their counts: "
                        + "it reproduces the fifteen period-eight classes and the twenty-six "
                        + "period-nine classes exactly.")),
                Describe.Lean(
                    DescribeId.Create("period-ten-orbit-01-has-a-low-arm"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_ten_orbit_01_low_arm"),
                    H("Enumeration Ten Maximin A"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Two proof shapes are needed and the split differs from period nine: twenty-two low states sit on the left branch and twenty on the right. The right-branch set was measured for this level."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB")),
            ]));
    }
}
