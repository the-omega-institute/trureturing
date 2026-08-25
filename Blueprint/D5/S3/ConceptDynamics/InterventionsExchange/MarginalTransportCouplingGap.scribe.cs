using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class MarginalTransportCouplingGapDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal single-world intervention marginals can transport while cross-world "
            + "agreement changes.",
        H("Marginal Transport and Coupling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marginal-transport-does-not-determine-coupling"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "marginal_transport_does_not_determine_coupling"),
                H("Marginal transport does not determine coupling transport"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The stable model returns the exogenous bit under both treatments. "
                            + "The flip model preserves it under false treatment and "
                            + "complements it under true treatment.")),
                    Paragraph(Text(
                        "Both models therefore have one false and one true outcome under "
                            + "each single-world intervention. Their intervention-count "
                            + "tables coincide.")),
                    Paragraph(Text(
                        "The coupling query uses the same uniform two-unit exogenous "
                            + "population. The two potential outcomes always agree in the "
                            + "stable model and never agree in the flip model, so the "
                            + "agreement probabilities differ."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stable = F.Id("noEffectModel");
        Formula flip = F.Id("flipEffectModel");
        Formula sameMarginals = Equal(Call("Int", stable), Call("Int", flip));
        Formula differentAgreement = NotEqual(
            Call("couplingAgreementProbability", stable),
            Call("couplingAgreementProbability", flip));

        return Disp(Seq(
            sameMarginals, Sp, Land, Sp, differentAgreement, Dot));
    }
}
