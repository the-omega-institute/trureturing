using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137;

internal sealed class PreparedEJMCompleteMiniCut01137Bucket11Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket11.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut 01137 elimination bucket 11",
        H("Cut 01137 elimination bucket 11"),
        Blocks(
            Paragraph(Text("The residual lower table is PreparedEJMCompleteMiniCut01137Tables.normal16302 (e 13) (e 15) (e 18). The finite receipt quantifies over 4 independent four-valued arguments, preserving all their combinations.")),
            Paragraph(Text("The bucket inequality is applied pointwise to a single full event. The semantic root scales it by the nonnegative integer 6987435 and uses it as one min-plus elimination step.")),
            Node("lower-at", "lowerAt", "The residual function after this elimination",
                "The residual function is defined by PreparedEJMCompleteMiniCut01137Tables.normal16302 (e 13) (e 15) (e 18); it retains precisely the displayed event coordinates.", DescribeRole.Definition),
            Node("receipt", "receipt", "The complete finite bucket inequality",
                "For every tuple of values for x13, x15, x18, x19, the stored offset plus the residual table is at most the sum of the exact input tables. The proof reduces this finite inequality on all 256 tuples.", DescribeRole.Theorem),
            Node("inequality-at", "inequality_at", "Apply the inequality to the same original assignment",
                "The conclusion is (-732920220 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group16.normalizedAt e + PreparedEJMCompleteMiniCut01137Bucket08.lowerAt e. Its proof specializes receipt at the displayed coordinates of the same event; no prefix-compatibility hypothesis is needed for this pointwise table inequality.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
