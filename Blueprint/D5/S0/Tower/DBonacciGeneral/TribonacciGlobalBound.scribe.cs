using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralTribonacciGlobalBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var x = Id("x");
        var t = Id("t");
        var reals = Id("R");
        var minusOne = Subtract(Num(0), Num(1));
        var inverseT = new Formula.Power(t, minusOne);

        Formula Liminf(Formula point) =>
            Call("liminfAtTop", Call("tribonacciSurvivor", q, point));

        var endpointLiminf = Equal(Liminf(Num(1)), inverseT);
        var unrestrictedBoundFalse = new Formula.Not(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Relation(
                Liminf(x),
                FormulaRelationOperator.LessThanOrEqual,
                Call("championValue", t))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The unrestricted real-line Tribonacci champion upper bound is false.",
            H("Tribonacci Global-Bound Refutation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-terminal-point-liminf"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound."
                        + "tribonacci_survivor_one_liminf"),
                    H("The terminal point liminf is t inverse"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(endpointLiminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The final name is nearest to the omitted endpoint one. Its terminal "
                            + "gap scales by t inverse cubed every three levels, giving normalized "
                            + "survivor phases 1, t-1, and t inverse. The last phase is the exact "
                            + "filter liminf."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("unrestricted-tribonacci-global-bound-is-false"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound."
                        + "tribonacci_unrestricted_global_liminf_upper_bound_false"),
                    H("The unrestricted global upper bound is false"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(unrestrictedBoundFalse)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At the Tribonacci root, championValue(t) is (1-t inverse)/2, strictly "
                            + "below the endpoint liminf t inverse. Thus the requested statement "
                            + "for every real x cannot follow from a forbidden-region iteration: "
                            + "it is false for the frozen real-line survivor itself."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
