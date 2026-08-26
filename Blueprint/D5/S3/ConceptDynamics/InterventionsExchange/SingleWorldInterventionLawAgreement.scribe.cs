using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class SingleWorldInterventionLawAgreementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionsExchange/SingleWorldInterventionLawAgreement."
            + "single_world_perfect_intervention_laws_agree";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stable and flip Boolean models agree under every perfect single-world intervention.",
        H("Single-World Intervention-Law Agreement"),
        Blocks(Describe.Lean(
            DescribeId.Create("single-world-perfect-intervention-laws-agree"),
            DeclarationHandle.Create(Declaration),
            H("All perfect single-world intervention laws agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The displayed statement binds S to noEffectModel and F to "
                        + "flipEffectModel before either law is mentioned. Neither model "
                        + "identifier is free.")),
                Paragraph(Text(
                    "For each imposed treatment, both models give one occurrence of each "
                        + "Boolean outcome over the uniform exogenous population.")),
                Paragraph(Text(
                    "The second clause compares the complete endogenous joint count law under "
                        + "every perfect intervention. The intervention type includes operations "
                        + "fixing X and operations fixing Y."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stable = F.Id("S");
        Formula flip = F.Id("F");
        Formula treatment = F.Id("x");
        Formula outcome = F.Id("y");
        Formula intervention = F.Id("a");
        Formula jointOutcome = F.Id("z");
        Formula boolean = F.Id("Bool");
        Formula jointBoolean = Seq(boolean, Sp, Times, Sp, boolean);

        Formula marginalClause = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("y"),
                boolean,
                new Formula.Logic(
                    Equal(Call("Int", stable, treatment, outcome), D(1)),
                    FormulaLogicOperator.And,
                    Equal(Call("Int", flip, treatment, outcome), D(1)))));

        Formula jointClause = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            F.Id("PerfectIntervention"),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("z"),
                jointBoolean,
                Equal(
                    Call("endogenousLaw", stable, intervention, jointOutcome),
                    Call("endogenousLaw", flip, intervention, jointOutcome))));

        Formula laws = new Formula.Logic(
            marginalClause,
            FormulaLogicOperator.And,
            jointClause);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("let")), Sp,
            stable, Sp, Colon, Eq, Sp, F.Id("noEffectModel"), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            flip, Sp, Colon, Eq, Sp, F.Id("flipEffectModel"), Comma,
            RowBreak, Grp(),
            laws, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
