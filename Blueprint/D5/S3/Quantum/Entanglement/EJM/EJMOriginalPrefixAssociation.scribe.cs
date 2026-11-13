using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalPrefixAssociationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Association of each original prefix cache and partial assignment",
        H("Association of each original prefix cache and partial assignment"),
        Blocks(
            Paragraph(Text("The prefix has twenty coordinates with four values each. Its cache starts with the original thirty-two local states and applies the same base-four digits as the partial assignment. Depth distinguishes leading zero values. Every natural code is allowed; only the lowest depth digits participate.")),
            Node("coordinate", "coordinate", "Coordinate at a prefix depth",
                "At depth d the coordinate is d modulo twenty. The two theorems restrict the prefix depth to at most twenty, so no assigned coordinate is revisited.", DescribeRole.Definition),
            Node("prefix-cache", "prefixCache", "Cache after the original prefix",
                "Depth zero uses the original initial cache. At depth d+1, apply the cache step at coordinate d to the cache for code divided by four, using code modulo four as the next outcome.", DescribeRole.Definition),
            Node("prefix-partial", "prefixPartial", "Partial assignment after the same prefix",
                "Depth zero leaves every coordinate unassigned. The successor updates the same coordinate with the same outcome as prefixCache.", DescribeRole.Definition),
            Node("prefix-partial-future-none", "prefixPartial_future_none", "Future coordinates remain unassigned",
                "For every depth at most twenty, every natural code and every coordinate whose value is at least that depth, prefixPartial returns none. Depth induction keeps the next coordinate distinct from each future coordinate.", DescribeRole.Theorem),
            Node("prefix-associated", "prefix_associated", "The cache represents the same complete prefix",
                "For every depth at most twenty and every natural code, prefixCache and prefixPartial satisfy AssociatedCache. The proof starts with initial_associated and applies step_associated at the previously unassigned coordinate. It does not assume a bound on the code.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
