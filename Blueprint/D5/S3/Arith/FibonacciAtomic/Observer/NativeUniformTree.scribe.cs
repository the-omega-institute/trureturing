using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformtree-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformTree", H("NativeUniformTree"), Blocks(
            Paragraph(Text("All tree operations use fixed preorder codes. Decreasing recursion carries addresses through symbolic cutting, and finite iteration evaluates each actual history epoch. The computation accepts every finite address and history without a consistency premise.")),
            Entry("term_at_prim", "Primitive recursive address navigation returns exactly the original native subtree option on every finite term and address.", DescribeRole.Theorem),
            Entry("tree_word_prim", "The fixed tree instance makes its preorder constructor word primitive recursive. The constructor word supplies recursion measures and output words.", DescribeRole.Theorem),
            Entry("symbolic_exterior_prim", "Primitive recursion on decreasing subtree words constructs the exact symbolic exterior while carrying original inherited addresses. Cut holes and every residual variable are retained.", DescribeRole.Theorem),
            Entry("readout_prim", "The original native four-valued readout is primitive recursive on every finite address and actual Source, including the empty address and blocked suffixes.", DescribeRole.Theorem),
            Entry("substitution_prim", "The original leaf substitution, extended over actual ordered pairs, is primitive recursive on the fixed native tree representation. Natural iteration evaluates arbitrary supplied counts.", DescribeRole.Theorem),
            Entry("history_consistent_prim", "Primitive recursion computes each requested substitution epoch and exact readout, then checks every finite history entry. Empty histories, repeated observations, absent replies and inconsistent histories remain in scope.", DescribeRole.Theorem))));
}
