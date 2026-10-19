using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState;

internal sealed class LowerBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic vector lower summation and four exact literal child-cache totals",
        H("Generic vector lower summation and four exact literal child-cache totals"),
        Blocks(
            Paragraph(Text("Each Describe belongs to the actual source module and an existing named public declaration. The original Lean namespace, imports, options, statements and proofs are retained.")),
            Paragraph(Text("The consuming original context is depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes this context once along the original path from depth thirteen, prefix 5209 and node 17413. Its Raw002 response enters Responses110 and the original score lower-bound consumer. The sibling prefixes remain separate contexts.")),
            Paragraph(Text("This source preparation does not establish kernel acceptance, a scoped report, Scribe emission, a resource bound or measured speed. All original whole-cache transition and complete-context acceptance obligations remain.")),
            Paragraph(Text("sum_lower_vecCons separates one vector head from its tail using the existing Fin summation and Matrix projection laws. The four exact readouts expand all thirty-two signed literal lower fields. Each Branch derives its unchanged scale inequality from its matching exact total. Full local-cache equality and transitions are supplied separately by the other modules.")),
            Node("sum-lower-vecCons", "sum_lower_vecCons", "Sum of one cached-local vector constructor",
                "For arbitrary natural N and n, a head : CachedLocal N and a tail : Fin n \u2192 CachedLocal N, the sum of row.lower over Matrix.vecCons head tail equals head.row.lower plus the sum over the original tail. This generic identity retains every row parameter and is used by each exact child total.", DescribeRole.Theorem),
            Node("child0-lower-exact", "child0_lower_exact", "Exact lower total of the complete literal child cache 0",
                "EJMCacheState.lower childCache0 equals the integer 18606457232991810. The readout sums all sixteen triangle and sixteen singleton signed lower fields of that exact literal cache. Branch0 projects its nextCache outcome to this child, rewrites by this equality and checks the original scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child1-lower-exact", "child1_lower_exact", "Exact lower total of the complete literal child cache 1",
                "EJMCacheState.lower childCache1 equals the integer 1714852503522795. The readout sums all sixteen triangle and sixteen singleton signed lower fields of that exact literal cache. Branch1 projects its nextCache outcome to this child, rewrites by this equality and checks the original scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child2-lower-exact", "child2_lower_exact", "Exact lower total of the complete literal child cache 2",
                "EJMCacheState.lower childCache2 equals the integer 10062141904509240. The readout sums all sixteen triangle and sixteen singleton signed lower fields of that exact literal cache. Branch2 projects its nextCache outcome to this child, rewrites by this equality and checks the original scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child3-lower-exact", "child3_lower_exact", "Exact lower total of the complete literal child cache 3",
                "EJMCacheState.lower childCache3 equals the integer 10896463891502280. The readout sums all sixteen triangle and sixteen singleton signed lower fields of that exact literal cache. Branch3 projects its nextCache outcome to this child, rewrites by this equality and checks the original scale 6987435 inequality.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
