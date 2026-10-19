using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037;

internal sealed class LowerBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four exact complete-cache lower totals for original prefix 5335037",
        H("Four exact complete-cache lower totals for original prefix 5335037"),
        Blocks(
            Paragraph(Text("Each Describe belongs to the actual source module and an existing named public declaration. The original Lean namespace, imports, options, statements and proofs are retained. Private receipts and private helpers receive no public wrappers.")),
            Paragraph(Text("This module belongs to the complete original context at depth eighteen, base-four prefix 5335037, node 442 and remaining fuel three. Its own parent cache, four children and partial assignment remain separate from the other prefixes reaching the same node.")),
            Paragraph(Text("At depth seventeen, prefix 1333759 and node 1305, this context is original outcome 1. Its complete accepted theorem supplies that ordered child to Raw002Tail442/Assembly.raw_cut_00337, which assembles the original context at depth thirteen, prefix 5209 and node 17413 together with every other original sibling along the four preceding outcome-three splits.")),
            Paragraph(Text("Complete-context acceptance retains this prefix's full prefix-cache equality, all four whole-cache steps, all four lower inequalities and original partial assignment. Shared node 442 fixes the replay node only. Reusing an opaque canonical row supplies its indexed full-row equality; the remaining State, cache and prefix-context obligations are earned separately for this prefix.")),
            Paragraph(Text("The source reuses CanonicalState.LowerBounds.sum_lower_vecCons to expand the vector sums and retains every signed lower entry. Only its four public exact totals receive Describe nodes here. The branches derive scale inequalities from these totals while whole-cache equality and transitions retain their separate proofs.")),
            Node("child0-lower-exact", "child0_lower_exact", "Exact lower total of the complete child cache 0",
                "For prefix 5335037, EJMCacheState.lower childCache0 equals the integer 20686156202449920. The readout sums the signed lower fields of all sixteen triangle and sixteen singleton placements of this exact cache. Branch0 projects its nextCache outcome to this child, rewrites by the exact equality and checks the unchanged scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child1-lower-exact", "child1_lower_exact", "Exact lower total of the complete child cache 1",
                "For prefix 5335037, EJMCacheState.lower childCache1 equals the integer 1002147724083870. The readout sums the signed lower fields of all sixteen triangle and sixteen singleton placements of this exact cache. Branch1 projects its nextCache outcome to this child, rewrites by the exact equality and checks the unchanged scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child2-lower-exact", "child2_lower_exact", "Exact lower total of the complete child cache 2",
                "For prefix 5335037, EJMCacheState.lower childCache2 equals the integer 16997489943731115. The readout sums the signed lower fields of all sixteen triangle and sixteen singleton placements of this exact cache. Branch2 projects its nextCache outcome to this child, rewrites by the exact equality and checks the unchanged scale 6987435 inequality.", DescribeRole.Theorem),
            Node("child3-lower-exact", "child3_lower_exact", "Exact lower total of the complete child cache 3",
                "For prefix 5335037, EJMCacheState.lower childCache3 equals the integer 14735460027853110. The readout sums the signed lower fields of all sixteen triangle and sixteen singleton placements of this exact cache. Branch3 projects its nextCache outcome to this child, rewrites by the exact equality and checks the unchanged scale 6987435 inequality.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
