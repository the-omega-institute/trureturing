using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFWedgesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFWedges.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of a finite vertex type. The definitions of tips and wedges apply to every such H. Under DUF and the cap of at most four neighbors per ground pair, two distinct edges in F(S) with card(S)=4 meet at a center. Their two remaining endpoints determine a four-edge common link. Recovering its center and leaves removes any overcounting.",
        H("Unordered wedges and four-edge common links"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tips"),
                DeclarationHandle.Create(Prefix + "tips"),
                H("The two noncentral endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The tips of a finite set family are the vertices in its union but not in its intersection. For a star with two leaves and center outside them, this is exactly the leaf pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wedges"),
                DeclarationHandle.Create(Prefix + "wedges"),
                H("Unordered fiber wedges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each four-element neighborhood S, take the two-element subfamilies of F(S). The index S and the unordered two-edge family together specify one wedge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wedge-structure"),
                DeclarationHandle.Create(Prefix + "wedge_structure"),
                H("From a wedge to a common link"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap, a four-element set S, and a two-element subfamily w of F(S), there are a center c and a two-element set q with c outside both q and S, w=cq, tips(w)=q, K(q)=cS, and card(K(q))=4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wedge-bijection"),
                DeclarationHandle.Create(Prefix + "wedge_bijection"),
                H("The exact wedge bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap, taking tips is a bijection between unordered fiber wedges indexed by four-element sets S and ground pairs with four-edge common links. Consequently their number q4 equals the sum over all four-element S of binom(card(F(S)),2). The uniqueness argument uses the center of a four-edge star, not a center choice for singleton stars."))),
                DescribeRole.Theorem)),
        []));
}
