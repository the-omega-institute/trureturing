using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class TypedDefinitionGraphSliceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/TypedDefinitionGraphSlice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dependency slice can strictly enlarge its target set.",
        H("Typed Definition Graph Slice"),
        Blocks(Describe.Lean(
            DescribeId.Create("dependency-slice-strict-witness"),
            DeclarationHandle.Create(Prefix + "dependencySlice_strict_witness"),
            H("Dependency slicing can strictly add prerequisites"),
            StatementSource.FromAuthor(StrictWitnessFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "In the concrete two-node typed definition graph, false is a direct "
                        + "prerequisite of true and the target set contains only true. The "
                        + "reflexive-transitive predecessor slice therefore also contains false.")),
                Paragraph(Text(
                    "This witnesses proper containment rather than only the general inclusion of "
                        + "targets in their dependency slice."))),
            DescribeRole.Theorem))));

    private static Formula StrictWitnessFormula() => Disp(Seq(
        F.Id("twoNodeTargets"), Sp, Subset, Sp,
        Call(
            "dependencySlice",
            F.Id("twoNodeDefinitionGraph"),
            F.Id("twoNodeTargets")),
        Dot));
}
