using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class PhaseAuditDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var k = Id("k");
        var naturals = Id("N");
        var phi = Id("phi");
        var sqrtFive = Call("sqrt", Num(5));
        var half = new Formula.Fraction(Num(1), Num(2));
        var auditPoint = new Formula.Fraction(Num(1), Add(phi, Num(2)));
        var evenValue = new Formula.Fraction(Num(1), Multiply(phi, sqrtFive));
        var lowOddValue = new Formula.Fraction(
            Num(1),
            Multiply(new Formula.Power(phi, Num(2)), sqrtFive));
        var championPoint = Subtract(
            new Formula.Fraction(Num(13), Num(2)),
            Multiply(Num(4), phi));
        var inversePhiHalf = new Formula.Fraction(
            new Formula.Power(phi, Subtract(Num(0), Num(1))),
            Num(2));
        var inversePhiSquaredHalf = new Formula.Fraction(
            new Formula.Power(phi, Subtract(Num(0), Num(2))),
            Num(2));

        Formula Arm(Formula q, Formula point) =>
            Call("goldenSurvivor", q, point);

        var evenPhases = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            Equal(
                Arm(Multiply(Num(2), Add(k, Num(1))), auditPoint),
                evenValue));
        var oddPhases = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            new Formula.Logic(
                Equal(
                    Arm(Add(Multiply(Num(4), k), Num(1)), auditPoint),
                    new Formula.Fraction(Num(1), sqrtFive)),
                FormulaLogicOperator.And,
                Equal(
                    Arm(Add(Multiply(Num(4), k), Num(3)), auditPoint),
                    lowOddValue)));
        var auditIdentity = Equal(auditPoint, evenValue);
        var demotion = new Formula.Logic(
            evenPhases,
            FormulaLogicOperator.And,
            new Formula.Logic(
                oddPhases,
                FormulaLogicOperator.And,
                auditIdentity));

        var championMembership = Call(
            "memberOf",
            championPoint,
            Call("goldenSurvivorMaximizers", Num(6)));
        var armRing = new Formula.Logic(
            Equal(Arm(Num(5), championPoint), inversePhiHalf),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(Arm(Num(6), championPoint), half),
                FormulaLogicOperator.And,
                Equal(Arm(Num(7), championPoint), inversePhiSquaredHalf)));
        var restoration = new Formula.Logic(
            championMembership,
            FormulaLogicOperator.And,
            armRing);
        var statement = new Formula.Logic(
            demotion,
            FormulaLogicOperator.And,
            restoration);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact phase discipline demotes the false constant-arm point and restores the champion.",
            H("Golden Phase Audit"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-phase-audit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/PhaseAudit.golden_phase_audit"),
                    H("Golden phase audit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The point 1/(phi+2) has one exact arm on every positive even "
                            + "level. Its two odd residue classes have distinct exact arms, "
                            + "so the former constant-arm claim fails with period four. The "
                            + "identity phi*sqrt(5)=phi+2 records the even value exactly.")),
                        Paragraph(Text(
                            "The frozen closed-form point 13/2-4*phi belongs to the level-six "
                            + "golden-survivor maximizer family. Its consecutive level-five, "
                            + "level-six, and level-seven arms are phi^(-1)/2, 1/2, and "
                            + "phi^(-2)/2, the exact form of the reported three-phase ring."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/MetricGeometry/GoldenSurvivorSet")),
            ]));
    }
}
