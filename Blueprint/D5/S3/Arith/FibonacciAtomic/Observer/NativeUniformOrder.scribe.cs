using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformorder-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformOrder", H("NativeUniformOrder"), Blocks(
            Paragraph(Text("The comparator is the original Boolean-list lexicographic order. Filtering, native rightmost deduplication and insertion sorting preserve the exact finite-set ordering used by symbolicOrdered.")),
            Entry("address_lt_prim", "A decreasing recursion over pairs of finite Boolean addresses decides the original native lexicographic strict order.", DescribeRole.Theorem),
            Entry("address_le_prim", "The non-strict comparator combines native strict order and equality for canonical insertion sorting.", DescribeRole.Theorem),
            Entry("symbolic_ordered_prim", "Primitive filtering, deduplication and sorting produce exactly the native list of reached cut addresses for arbitrary finite input lists, including duplicates and unsorted addresses.", DescribeRole.Theorem))));
}
