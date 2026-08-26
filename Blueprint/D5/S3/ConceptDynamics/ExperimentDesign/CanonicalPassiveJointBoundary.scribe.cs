using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class CanonicalPassiveJointBoundaryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/CanonicalPassiveJointBoundary."
            + "canonical_adaptive_cost_reduction_and_passive_boundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptivity lowers cost but cannot cross the canonical passive joint boundary.",
        H("Canonical Passive Joint Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-adaptive-cost-and-passive-boundary"),
            DeclarationHandle.Create(Declaration),
            H("Adaptivity cannot cross the complete passive boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The modular four-state witness has adaptive depth strictly below its "
                        + "minimum exact fixed-suite depth, so adaptive selection can reduce "
                        + "experiment cost.")),
                Paragraph(Text(
                    "For an arbitrary passive experiment family, every deterministic adaptive "
                        + "transcript factors through the canonical joint readout. A target that "
                        + "does not refine that readout therefore cannot refine any such transcript.")),
                Paragraph(Text(
                    "Crossing this boundary requires leaving the quantified class through new "
                        + "experiments, a changed object, intervention, expanded observations, "
                        + "or an added domain premise. The proof directly applies the frozen "
                        + "family theorem and redeclares no protocol or readout primitive."))),
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
