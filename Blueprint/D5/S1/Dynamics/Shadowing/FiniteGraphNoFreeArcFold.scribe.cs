using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphNoFreeArcFoldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local injectivity in the open edges of finite graphs",
        H("Local injectivity in the open edges of finite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("no-fold-in-finite-graph-open-edge"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold.isLocallyInjective_iterate_at_openEdge"),
            H("Every positive iterate is locally injective along each open edge"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A collision of an iterate inside a sufficiently short free arc yields a strict local fold after isolating its finite fiber. Strong transitivity pulls the fold into any open subarc. The two disjoint lifts of a common shorter arc then double a close coalescing family. Arbitrary repetition would violate the uniform cardinal bound on forward Bowen balls."))),
            DescribeRole.Theorem))));
}
