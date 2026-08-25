using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentBoundary;

internal sealed class PassiveJointBoundaryObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction."
            + "adaptive_cost_reduction_and_passive_boundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive protocols can reduce query cost, but passive transcripts remain "
            + "bounded by the complete joint experiment readout.",
        H("Adaptive Cost and the Passive Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("adaptive-cost-reduction-and-passive-boundary"),
            DeclarationHandle.Create(Declaration),
            H("Adaptivity cannot cross the complete passive boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The modular four-state witness has minimum adaptive depth two "
                        + "and minimum fixed-suite cardinality three, so adaptive "
                        + "selection can strictly lower experiment cost.")),
                Paragraph(Text(
                    "For an arbitrary passive experiment family, every deterministic "
                        + "adaptive transcript is replayable from the complete dependent "
                        + "tuple of experiment answers. Any recovery from the transcript "
                        + "would therefore recover the target from that complete tuple.")),
                Paragraph(Text(
                    "The quantified protocol class keeps the experiment family, state "
                        + "carrier, response carriers, readout channels, and admitted "
                        + "domain fixed. A successful scheme beyond this boundary must "
                        + "leave that class through new experiments, a changed object, "
                        + "intervention, expanded observations, or an added domain premise."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula experimentType = F.Id("U");
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("Y");
        Formula response = F.Id("R");
        Formula experiment = F.Id("u");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula protocol = F.Id("pi");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula responseAt = new Formula.Subscript(response, experiment);
        Formula adaptiveDepth = new Formula.Subscript(F.Id("D"), F.Id("ad"));
        Formula staticDepth = new Formula.Subscript(F.Id("D"), F.Id("stat"));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, experimentType, Comma, Sp, stateType, Comma, Sp,
                targetType, Colon, Sp, type, Comma, Sp,
                response, Colon, Sp, experimentType, Sp, To, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, experiment, Colon, Sp,
                experimentType, Comma, Sp, stateType, Sp, To, Sp, responseAt,
                Comma, Sp, target, Colon, Sp, stateType, Sp, To, Sp, targetType,
                Comma),
            Seq(
                Neg, Call("Refines", target, Call("jointReadout", readout)),
                Sp, Implies, Sp),
            Seq(
                adaptiveDepth, Sp, Lt, Sp, staticDepth, Sp, Land, Sp,
                Neg, Exists, Sp, protocol, Colon, Sp,
                Call("PassiveProtocol", experimentType, response), Comma, Sp,
                Call(
                    "Refines",
                    target,
                    Call("runPassiveProtocol", readout, protocol)),
                Dot),
        ]));
    }
}
