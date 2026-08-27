using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class DiscretionaryOutcomeNonuniquenessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness."
            + "discretionary_outcome_nonuniqueness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A public-law fiber with two licensed outcomes does not determine a unique result.",
        H("Discretionary Outcome Nonuniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("discretionary-outcome-nonuniqueness"),
            DeclarationHandle.Create(Declaration),
            H("A hard case has no uniquely determined outcome"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The outcome predicate is constructed directly from admissibility, the "
                        + "public-law readout, and the permission relation.")),
                Paragraph(Text(
                    "Two distinct outcomes satisfying that same predicate contradict any "
                        + "claim of unique existence. A determinate choice therefore needs "
                        + "information or a selection rule beyond the public interface."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula caseType = F.Id("Case");
        Formula factType = F.Id("PublicFact");
        Formula outcomeType = F.Id("Outcome");
        Formula publicLaw = F.Id("publicLaw");
        Formula admissible = F.Id("admissible");
        Formula permitted = F.Id("permitted");
        Formula fact = F.Id("b");
        Formula left = F.Id("y0");
        Formula right = F.Id("y1");
        Formula chosen = F.Id("y");
        Formula leftCase = F.Id("x0");
        Formula rightCase = F.Id("x1");
        Formula witnessCase = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula Apply(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula Allowed(Formula x, Formula y) =>
            Seq(
                Apply(admissible, x), Sp, Land, Sp,
                Equal(Apply(publicLaw, x), fact), Sp, Land, Sp,
                Call("permitted", x, y));
        Formula ExistsAllowed(Formula x, Formula y) =>
            Seq(Exists, Sp, x, Colon, Sp, caseType, Comma, Sp, Allowed(x, y));
        Formula multiple = Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, outcomeType, Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Open, ExistsAllowed(leftCase, left), Close, Sp, Land, Sp,
            Open, ExistsAllowed(rightCase, right), Close);
        Formula unique = Seq(
            Exists, Sp, Bang, Sp, chosen, Colon, Sp, outcomeType, Comma, Sp,
            ExistsAllowed(witnessCase, chosen));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, caseType, Comma, Sp, factType, Comma, Sp,
                outcomeType, Colon, Sp, type, Comma),
            Seq(
                publicLaw, Colon, Sp, caseType, Sp, To, Sp, factType, Comma, Sp,
                admissible, Colon, Sp, caseType, Sp, To, Sp, prop, Comma),
            Seq(
                permitted, Colon, Sp, caseType, Sp, To, Sp,
                outcomeType, Sp, To, Sp, prop, Comma, Sp,
                fact, Colon, Sp, factType, Comma),
            Seq(Open, multiple, Close, Sp, Implies),
            Seq(Neg, Open, unique, Close, Dot),
        ]));
    }
}
