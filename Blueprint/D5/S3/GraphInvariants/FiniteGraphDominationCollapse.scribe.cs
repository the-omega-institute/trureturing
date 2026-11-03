using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.GraphInvariants;

internal sealed class FiniteGraphDominationCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/GraphInvariants/FiniteGraphDominationCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous domination gives finite elementary collapses of the original labelled independence complex.",
        H("Finite graph domination and elementary collapse"),
        Blocks(
            Describe.Lean(DescribeId.Create("elementary-collapse"),
                DeclarationHandle.Create("D5/S3/GraphInvariants/FiniteGraphDominationCollapse.ElementaryCollapse"),
                H("A codimension-one free pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any vertex type V with decidable equality and pre-abstract complexes K,L on V, "
                    + "ElementaryCollapse(K,L) means that there are a nonempty finite face sigma of K "
                    + "and a vertex a absent from sigma, such that insert(a,sigma) is a face of K, "
                    + "every proper coface of sigma in K equals insert(a,sigma), and for every tau, "
                    + "tau is in L exactly when it is in K and equals neither of those two faces. "
                    + "The upper face has exactly one more vertex. Both complexes use nonempty faces "
                    + "and may omit ambient singleton faces."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-collapses"),
                DeclarationHandle.Create("D5/S3/GraphInvariants/FiniteGraphDominationCollapse.Collapses"),
                H("Finite collapse sequences"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any decidable vertex type V, Collapses is Relation.ReflTransGen of "
                    + "ElementaryCollapse on PreAbstractSimplicialComplex V. Thus every sequence "
                    + "is finite, with the reflexive case allowing zero steps."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("domination-collapse"),
                DeclarationHandle.Create(Prefix + "domination_collapses"),
                H("Simultaneous open-neighborhood domination"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every universe u, finite type V : Type u with decidable equality, "
                    + "simple graph G on V, vertex a and finite set D of vertices, assume a is not "
                    + "in D and the open neighborhood of a is contained in that of each d in D. "
                    + "Then the underlying pre-abstract independence complex of G collapses to "
                    + "FiniteGraphVertexSubstitution.restricted(G, fun x => x not in D), "
                    + "on the original carrier V. No ordering or independence of D is assumed. "
                    + "The case D empty is the reflexive sequence.")), Paragraph(Text(
                    "Pair every independent face meeting D and omitting a with its insertion of a. "
                    + "If an edge from a reached a vertex of such a face, domination would give "
                    + "an edge from a deleted vertex already in the face; independence and "
                    + "looplessness exclude this, so the upper face is independent. Erasing a "
                    + "from an upper face still leaves a vertex of D and hence a nonempty lower face. "
                    + "The pairs are disjoint and exhaust exactly the faces meeting D.")), Paragraph(Text(
                    "At each stage keep a valid current pre-abstract complex and the finite family "
                    + "of remaining lower faces. Choose a lower face of maximum cardinality. "
                    + "A surviving proper coface cannot avoid a, since it would be a larger lower "
                    + "face; after erasing a, the same argument makes any coface containing a "
                    + "its designated upper face. Deleting exactly this pair preserves downward "
                    + "closure: a surviving face containing a deleted lower face would have to be "
                    + "the deleted upper face. Strong induction on the finite remaining family "
                    + "terminates after erasing one pair per step. The final face equality is "
                    + "the original-carrier restricted complex."))), DescribeRole.Theorem),
            Paragraph(Text(
                "Elementary simplicial collapse and the domination argument are classical; "
                + "no novelty is claimed. The source discussion C-28.8 and C-28.L in "
                + "AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS gives a path "
                + "free-coface deletion argument and cites Ehrenborg and Hetyei, The topology "
                + "of the independence complex, European Journal of Combinatorics 27 (2006), "
                + "906-923, DOI 10.1016/j.ejc.2005.04.010, Section 2 and its path results. "
                + "That discussion supplies motivation and classical attribution; it does not "
                + "state this arbitrary simultaneous-deletion theorem. The present conclusion "
                + "asserts the combinatorial collapse sequence, without a realization or forest classification.")))));
}
