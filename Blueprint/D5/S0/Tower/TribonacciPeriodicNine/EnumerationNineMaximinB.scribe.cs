using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicNine;

internal sealed class EnumerationNineMaximinBDocument : IScribeDocumentDefinition
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
                new Formula.Relation(
                    Call("tribonacciPeriodicStateArm",
                        Call("decodeTribonacciState", Call("lowState", orbit))),
                    FormulaRelationOperator.LessThanOrEqual,
                    Call("championValue", Id("t")))));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-nine orbits N through Z have a low arm at or below the champion value.",
            H("Enumeration Nine Maximin B"),
            Blocks(
                Paragraph(Text(
                    "Two proof shapes are needed, not one. The recorded low state lies on the "
                        + "left branch of the arm minimum for fourteen orbits and on the right "
                        + "branch for twelve. Which branch applies was measured per orbit rather "
                        + "than assumed; an earlier draft used a different and wrong twelve, and "
                        + "the K case failed to close.")),
                Describe.Lean(
                    DescribeId.Create("every-period-nine-orbit-has-a-low-arm"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_nine_low_arms_bounded"),
                    H("Enumeration Nine Maximin B"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This converts into a theorem what the enumerator had only checked "
                            + "numerically, and it is what makes the certificates usable: no "
                            + "representative is a strict survivor."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineValid")),
            ]));
    }
}
