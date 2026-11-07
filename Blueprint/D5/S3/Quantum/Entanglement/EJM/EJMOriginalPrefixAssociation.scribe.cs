using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalPrefixAssociationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Association of each original prefix cache and partial assignment",
        H("Association of each original prefix cache and partial assignment"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
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
