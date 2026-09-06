using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class BranchingPotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core branching, exact certificates and their precise scope.",
        H("BranchingPotential"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-branchingpotential-childweight"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/BranchingPotential.childWeight"),
                H("Weighted children"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Absent children contribute zero. Each direction is counted separately, even when multiple directions reach one state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-branchingpotential-pathcount"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/BranchingPotential.pathCount"),
                H("Controlled descendants"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The policy sees both the current state and the complete newest-first direction history. Depth zero counts the current node once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-branchingpotential-upper-of-superpotential"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/BranchingPotential.upper_of_superpotential"),
                H("A positive super-potential bounds all depths"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer one-step inequalities for the selected actions imply an explicit all-depth upper bound by induction. The concrete geometric controller is supplied in RadiusThreeCertificates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-branchingpotential-lower-of-subpotential"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/BranchingPotential.lower_of_subpotential"),
                H("A bounded sub-potential bounds all depths from below"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weights may vanish on dead states. A cap on every weight and row inequalities at every history imply the lower bound. Requiring all actions at every state makes the result uniform over history-dependent policies."))),
                DescribeRole.Theorem),
            Paragraph(Text("The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.")))));
}
