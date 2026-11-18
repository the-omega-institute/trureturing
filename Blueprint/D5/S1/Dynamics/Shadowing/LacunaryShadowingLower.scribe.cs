using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LacunaryShadowingLowerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/LacunaryShadowingLower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp lower bound on tracer cardinality", H("The sharp lower bound on tracer cardinality"), Blocks(
        Paragraph(Text("The initial diameter condition forces a common occupied initial coordinate and thereby leaves each genuine tracer room for only one later target.")),
        Describe.Lean(DescribeId.Create("lacunary-not-neighborhood-smaller"), DeclarationHandle.Create(Owner + "lacunary_not_neighborhood_smaller"), H("No neighborhood (m-2)-shadowing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every m>=3, choose one fixed positive accuracy small enough to force agreement at coordinate zero. For every pseudo-orbit tolerance, truncate the support {0,q,...,(m-1)q} in a short moving window, with q a sufficiently large power of m+1. Each state has at most one occupied coordinate and is legal; neighboring states agree on the tolerance window. Initial tracing and small initial diameter force every tracer to equal one at zero. Its defining m-term constraint then permits at most one of the remaining m-1 targets. Selecting a tracer for each target gives an injection of Fin(m-1) into the tracing set, contradicting a cardinality at most m-2. The obstruction excludes every eligible fixed tracing set."))), DescribeRole.Theorem))));
}
