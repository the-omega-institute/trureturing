using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class FactualInterventionConsistencyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionsExchange/FactualInterventionConsistency."
            + "factual_intervention_consistency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factual outcome agrees with the potential outcome at the matching treatment.",
        H("Factual Intervention Consistency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factual-intervention-consistency"),
                DeclarationHandle.Create(Declaration),
                H("The factual outcome agrees with the matching intervention"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The factual and intervened outcomes are evaluations of one shared "
                            + "structural mechanism at the same exogenous state.")),
                    Paragraph(Text(
                        "When the factual treatment equals the imposed value, equality "
                            + "transport through that mechanism identifies the outcomes."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula exogenousType = F.Id("U");
        Formula treatmentType = F.Id("X");
        Formula outcomeType = F.Id("Y");
        Formula mechanism = F.Id("f");
        Formula assignment = F.Id("XFact");
        Formula exogenous = F.Id("u");
        Formula treatment = F.Id("x");
        Formula imposed = F.Id("xPrime");
        Formula factualOutcome = F.Id("YFact");
        Formula potentialOutcome = F.Id("YPot");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, exogenousType, Comma, Sp, treatmentType, Comma, Sp,
            outcomeType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            mechanism, Colon, Sp, exogenousType, Sp, To, Sp, treatmentType,
            Sp, To, Sp, outcomeType, Comma, Sp,
            assignment, Colon, Sp, exogenousType, Sp, To, Sp, treatmentType,
            Comma, RowBreak, Grp(),
            exogenous, Colon, Sp, exogenousType, Comma, Sp,
            treatment, Colon, Sp, treatmentType, Comma, RowBreak, Grp(),
            Apply(assignment, exogenous), Sp, Eq, Sp, treatment,
            Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            factualOutcome, Sp, Colon, Eq, Sp,
            Apply(mechanism, exogenous, Apply(assignment, exogenous)),
            Comma, Sp,
            potentialOutcome, Open, imposed, Close, Sp, Colon, Eq, Sp,
            Apply(mechanism, exogenous, imposed), Close, SemiSpace,
            RowBreak, Grp(),
            factualOutcome, Sp, Eq, Sp, Apply(potentialOutcome, treatment), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
