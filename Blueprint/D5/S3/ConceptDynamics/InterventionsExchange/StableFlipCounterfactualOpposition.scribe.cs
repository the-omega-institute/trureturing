using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class StableFlipCounterfactualOppositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionsExchange/StableFlipCounterfactualOpposition."
            + "stable_flip_intervention_equivalent_counterfactual_opposite";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable and flip models agree on every single-world intervention law while "
            + "their potential outcomes have opposite couplings.",
        H("Stable and Flip Counterfactual Opposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("stable-flip-intervention-equivalent-counterfactual-opposite"),
            DeclarationHandle.Create(Declaration),
            H("Single-world equivalence with opposite counterfactual coupling"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The stable and flip names are bound to the canonical finite Boolean "
                        + "models before any probability or law is stated.")),
                Paragraph(Text(
                    "Agreement probability is computed on the same uniform two-unit "
                        + "exogenous population. Its complement is the disagreement "
                        + "probability.")),
                Paragraph(Text(
                    "The intervention clause compares the full endogenous joint count law "
                        + "for every perfect intervention on either variable. The final "
                        + "clause compares the unit-preserving counterfactual profiles."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stable = F.Id("S");
        Formula flip = F.Id("F");
        Formula agreement = F.Id("couplingAgreementProbability");
        Formula stableAgreement = Call(agreement, stable);
        Formula flipAgreement = Call(agreement, flip);
        Formula intervention = F.Id("a");
        Formula result = F.Id("z");
        Formula boolean = F.Id("Bool");
        Formula jointBoolean = Seq(boolean, Sp, Times, Sp, boolean);

        Formula interventionClause = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            F.Id("PerfectIntervention"),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("z"),
                jointBoolean,
                Equal(
                    Call("endogenousLaw", stable, intervention, result),
                    Call("endogenousLaw", flip, intervention, result))));

        Formula clauses = new Formula.Logic(
            Equal(stableAgreement, D(1)),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(Seq(D(1), Sp, Minus, Sp, flipAgreement), D(1)),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    interventionClause,
                    FormulaLogicOperator.And,
                    NotEqual(Call("CF", stable), Call("CF", flip)))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("let")), Sp,
            stable, Sp, Colon, Eq, Sp, F.Id("noEffectModel"), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            flip, Sp, Colon, Eq, Sp, F.Id("flipEffectModel"), Comma,
            RowBreak, Grp(),
            clauses, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(name, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
