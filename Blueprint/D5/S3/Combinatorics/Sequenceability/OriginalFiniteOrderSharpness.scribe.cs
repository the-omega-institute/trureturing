using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class OriginalFiniteOrderSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite abelian labels attain the cyclic-order component bound.",
        H("Sharpness of the finite-order component bound"), Blocks(
            Describe.Lean(
                DescribeId.Create("finite-order-sharpness"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderSharpness.sharpness"),
                H("An extremal family for every cyclic order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m at least two, put J = Fin(m-1) and G = ZMod m times ((J to ZMod 2) times ZMod 2). The original coordinates are Option J summed with Option J. Write q = inl none, p = inr none, a_j = inl (some j), and b_j = inr (some j), and let Y contain all original coordinates. With e_j = Pi.single j 1, assign q the label (1,0,0), p the label (0,0,1), a_j the label (0,e_j,0), and b_j the label (-1,-e_j,0). This group is finite, the labeling is injective, every original label is nonzero, q belongs to Y, and its label has additive order exactly m.")),
                    Paragraph(Text("Every nonempty original coefficient-one zero support is exactly one triple {q,a_j,b_j}. To prove this, project its sum onto the last binary coordinate to exclude p. Projection onto coordinate j of the binary function gives the difference of the membership bits for a_j and b_j. The two unequal-bit cases are nonzero in ZMod 2, so the two coordinates occur together. If k pairs are present and epsilon is the membership bit of q, the first coordinate gives epsilon = k modulo m. Both natural representatives are less than m, since k is at most m-1 and epsilon is zero or one. Thus k = epsilon. Nonemptiness forces both to equal one, which gives the complete zero-support classification.")),
                    Paragraph(Text("Let E be exactly all proper original inclusion-minimal nonempty zero supports in Y. The classification shows that E is the image of the m-1 triples: each triple has zero sum, and any nonempty zero subset of one triple must be that same triple. The sentinel p makes every triple proper, including when m is two. Consequently E has m-1 elements, each contains q, and distinct punctures after deleting q are disjoint. Binary basis evaluations distinguish the a indices and the b indices; the first cyclic coordinate separates a labels from b labels, and the sentinel coordinate separates p.")),
                    Paragraph(Text("Use the canonical supportIntersectionGraph E q on all of E, and count the image of its connectedComponentMk on all q-containing vertices. Disjoint punctures make this graph empty. Reachability in the empty graph is equality, so the actual component map is injective and gives a lower bound of m-1 for this image. The theorem q_containing_component_card_lt supplies the upper bound strictly below m, because m annihilates the proved label of q. These two inequalities give exactly m-1 actual q-containing components. This proves optimality of the cyclic-order bound within finite abelian label groups, with injective nonzero labels and with all original minimal supports included.")),
                    Paragraph(Text("The construction and proof route are caller supplied. The formal proof adapts the Codex finite-binary source, SHA256 89322ebb5d7db149475a93d0a9783d6e9c78ce4ea49dd7761340aa08f85157bf, itself adapted from the integer-coordinate source, SHA256 08d642eaa8668bd03e7cd599073a8723cb0d68c733fa8799c9bda778ada3ba59. The upper bound is OriginalFiniteOrderComponentBound.q_containing_component_card_lt. The pair-balance and complete zero-support arguments give an unbounded structural construction, rather than a bounded enumeration. No literature novelty, good-ordering, or infinite-order conclusion is asserted.")))))));
}
