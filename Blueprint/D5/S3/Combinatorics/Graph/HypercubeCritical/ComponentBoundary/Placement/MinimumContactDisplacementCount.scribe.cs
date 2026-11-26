using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class MinimumContactDisplacementCountDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/"
        + "MinimumContactDisplacementCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting uniform displacement families from their extensions.",
        H("Three extensions give a sharp displacement count"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-contact-three-extension-count"),
            DeclarationHandle.Create(Owner + "card_and_eq_powerset_of_three_extensions"),
            H("The minimum size and its equality case"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let each member of a nonempty family have d axes, with d positive. "
                    + "Suppose each set obtained by deleting one axis extends to at least "
                    + "three members of the family. Then at least (d + 2) choose 2 members occur. "
                    + "Equality gives all the d-subsets of one set of d + 2 axes.")),
                Paragraph(Text("The family of members containing a given axis, with that axis "
                    + "removed, inherits the extension hypothesis. Induction bounds every "
                    + "nonempty such family. A single ridge and its three extensions already "
                    + "use d + 2 axes. Count the incidences between all used axes and family "
                    + "members to obtain the lower bound. In the equality case there are "
                    + "exactly d + 2 used axes, and the family fills their d-subsets."))),
            DescribeRole.Theorem))));
}
