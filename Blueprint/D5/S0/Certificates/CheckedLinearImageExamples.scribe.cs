using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CheckedLinearImageExamplesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/Certificates/CheckedLinearImageExamples.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete capped-coupling certificates and corrupted-input rejection checks.",
        H("Capped Coupling Certificate Replay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("capped-fixture-real-image"),
                DeclarationHandle.Create(Module + "capped_fixture_real_image"),
                H("A complete real interval from numerical evidence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RealQueryImage", F.Id("cappedMatrix"),
                        Call("cappedRhs", Fraction(1, 2), Fraction(2, 3), Fraction(1, 3)),
                        F.Id("jointObjective")), Eq,
                    Call("Icc", Fraction(5, 12), Fraction(1, 2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RealQueryImage is the image of all real vectors x satisfying the "
                        + "cast rational inequalities under the cast rational objective. The "
                        + "coordinate order is 00,01,10,11 and jointObjective is (0,0,0,1). "
                        + "There are no hypotheses.")),
                    Paragraph(Text(
                        "The eleven rows encode four nonnegative coordinates, total mass one "
                        + "in both directions, each marginal in both directions, and a "
                        + "disagreement cap. cappedRhs(p,q,delta) is "
                        + "(0,0,0,0,1,-1,p,-p,q,-q,delta).")),
                    Paragraph(Text(
                        "The accepted lower witness is (1/4,1/4,1/12,5/12) and the upper "
                        + "witness is (1/3,1/6,0,1/2). Lower multipliers put 1/2 on each "
                        + "negative marginal row and the cap row; upper multipliers put one "
                        + "on the first positive marginal row and on the 10 nonnegativity row. "
                        + "capped_payload_accepted is proved by kernel reduction and is "
                        + "consumed by checked_real_query_image.")),
                    Paragraph(Text(
                        "Four separate kernel-checked mutations reject a negated upper "
                        + "multiplier vector, a changed lower witness coordinate, a doubled "
                        + "objective coefficient, and a zero disagreement cap. The checker "
                        + "always receives the authoritative problem separately from the payload."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inconsistent-fixture-real-infeasible"),
                DeclarationHandle.Create(Module + "inconsistent_fixture_real_infeasible"),
                H("An accepted Farkas certificate excludes real solutions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Exists, Sp, F.Id("x"), Colon,
                    Call("Fin", F.D(4)), To, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Call("RealFeasible", F.Id("cappedMatrix"),
                        Call("cappedRhs", Fraction(3, 4), Fraction(1, 4), Fraction(1, 4)),
                        F.Id("x")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RealFeasible means every cast row inequality holds. The statement "
                        + "has no hypotheses. The weights are (0,2,0,0,0,0,0,1,1,0,1); "
                        + "their weighted columns vanish and the right-hand side is -1/4.")),
                    Paragraph(Text(
                        "inconsistent_payload_accepted checks this raw data by kernel "
                        + "reduction. checked_infeasible then excludes every real solution. "
                        + "These examples certify four-cell systems; they do not assert "
                        + "a structural causal interpretation or coverage of all ternary responses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Fraction(byte numerator, byte denominator) =>
        Seq(Frac, Grp(F.D(numerator)), Grp(denominator == 12 ? F.D(1, 2) : F.D(denominator)));
}
