using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.SpaceTime;

internal sealed class CommutingSpaceTimeActionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting spatial and temporal permutation actions combine into a product-monoid action.",
        H("Commuting Space-Time Action"),
        Blocks(
            Def("action", "SpaceTimeAction", "Commuting space-time representation",
                "Spatial and temporal monoids act by permutations on one state space and commute pointwise."),
            Def("joint", "jointAct", "Joint space-time action",
                "A spatial action is applied after the temporal action of the paired parameter."),
            Def("orbit", "jointOrbit", "Joint orbit",
                "The joint orbit contains every state reachable by one product space-time parameter."),
            Thm("identity", "jointAct_one", "Identity fixes every state",
                "The two identity parameters act as the identity permutation."),
            Thm("multiplication", "jointAct_mul", "Product parameters compose",
                "Commutation of the component actions makes joint action respect product-monoid multiplication."),
            Thm("commute", "pure_space_time_commute", "Pure space and time actions commute",
                "The joint embeddings of a spatial parameter and a temporal parameter commute on every state."),
            Thm("fixed", "joint_fixed_of_component_fixed", "Componentwise fixed states are jointly fixed",
                "A state fixed by both selected components is fixed by their joint action."),
            Thm("self-orbit", "self_mem_jointOrbit", "Every state lies in its orbit",
                "The identity space-time parameter witnesses reflexivity of the orbit relation.")),
        []));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
