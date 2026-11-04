using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class UnsignedStarSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/UnsignedStarSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least support of an unsigned integer star representative is exact original-edge bipartization, and its finite optimum is the complement of an indexed maximum cut.",
        H("Unsigned Star Support and Original Indexed Cuts"),
        Blocks(
            Describe.Lean(DescribeId.Create("color-support"),
                DeclarationHandle.Create(Prefix + "color_support"), H("Exact Support of the Boolean Potential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed supplier identity, exposed unchanged: the actual integer representative has support exactly the uncut original IDs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("color-bounds"),
                DeclarationHandle.Create(Prefix + "color_bounds"), H("Bounds for the Boolean Potential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed supplier bounds, exposed unchanged: potential values are 0 or -1 and representative values are -1, 0 or 1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-value-sign-cut"),
                DeclarationHandle.Create(Prefix + "odd_sign_cut"), H("The Existing Sign Witness Respects Equal Values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing sign witness decide(0 < 2*b(v)+1) now also records that equal integer potential values give equal colors. The original unrestricted support inclusion and old public conclusions are preserved. This supplier refinement is consumed by invariant compression; it is not claimed as a new independent mathematical result."))), DescribeRole.Theorem),
            Paragraph(Text("Use the existing loopless Edges V X carrier with integer starMap b(i)=b(left(i))+b(right(i)). "
                + "The representative is the actual integer vector z_b(i)=1+starMap b(i), without saturation or a quotient cancellation. "
                + "A Boolean partition c has cutEdges consisting of every original ID whose endpoint colors differ. "
                + "Parallel IDs have identical crossing decisions but each contributes one coordinate and one cardinal unit. "
                + "The total color potential is -1 on true and 0 on false, including isolated vertices.")),
            Describe.Lean(DescribeId.Create("bounded-support"),
                DeclarationHandle.Create(Prefix + "bounded_support_of_bipartite"),
                H("A Bipartite Remainder Produces a Bounded Potential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary vertex and original edge types and any deleted set D, bipartiteness of "
                    + "graphAfterDeleting D supplies an integer potential b with every b(v) equal to 0 or -1, "
                    + "every z_b(i) equal to -1, 0, or 1, and support(z_b) contained in D. Choose disjoint bipartition sets "
                    + "from Mathlib, color membership in one of them, and assign all remaining vertices the other color. "
                    + "Every undeleted original edge crosses this total partition, so its representative coordinate is zero. "
                    + "No connectedness, finiteness, or assumed coloring certificate is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-criterion"),
                DeclarationHandle.Create(Prefix + "support_subset_iff_bipartite"),
                H("Exact Support and Bipartite Deletion Criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists an unrestricted integer b with support(1+starMap b) contained in D "
                    + "if and only if graphAfterDeleting D is bipartite. For the forward implication form the odd integer "
                    + "a(v)=2*b(v)+1. Each a(v) is nonzero, and a zero representative coordinate forces the two endpoint "
                    + "values to sum to zero. Their signs therefore differ. The resulting total Boolean sign cut has "
                    + "all its uncut original IDs in support(z_b), hence in D, and supplies a bipartition after deletion. "
                    + "The reverse implication uses the bounded construction above. Disconnected remainders and infinite "
                    + "types are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attained-optimum"),
                DeclarationHandle.Create(Prefix + "attained_support_bipartization_maxcut"),
                H("Attained Integer Support, Edge Bipartization, and Maximum Cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When V and X are finite, a maximizing total Boolean partition c exists. Its 0/-1 "
                    + "potential attains the least support cardinality among all unrestricted integer potentials, and that "
                    + "same cardinality is the least size of an original-ID deletion leaving a bipartite graph. "
                    + "The theorem gives both IsLeast statements, an IsGreatest statement for the cut cardinalities, "
                    + "and the exact equality minimum support=card(X)-maximum cut. For every integer b, the odd-sign cut "
                    + "has uncut set contained in support(z_b); maximality of c therefore gives the lower bound for every b, "
                    + "including arbitrarily large coefficients. Conversely the color potential has support exactly the "
                    + "complement of its cut. The support criterion transfers attainment and the lower bound to all "
                    + "bipartizing deletions. All extrema count original IDs, including parallel multiplicity. "
                    + "The proof is symbolic finite extremization, with no enumeration algorithm or complexity assertion."))), DescribeRole.Theorem),
            Paragraph(Text("On a connected nonbipartite graph the existing UnsignedStarTorsion supplier identifies the full "
                + "indicator as a nonzero order-two class. The present result determines its least coordinate support. "
                + "It makes no full componentwise torsion classification, free or equivariant splitting, faithful action, "
                + "unrestricted original full-blocker, Good, or AM claim.")),
            Paragraph(Text("Attribution: caller-supplied Unsigned Incidence Torsion: Exact Support and Equivariance, "
                + "Sections 3-4, SHA256 c514b03ad862efd9a78b7509fa1b19e606f89a7bdf278e7ecfb8eed84192be9f. "
                + "This is a repository derivation relative to the existing integer star carrier and Mathlib bipartition "
                + "and finite-extremum contracts. The source argument is mathematical guidance; formal truth comes from "
                + "the compiled declarations. No literature-priority claim is made.")))));
}
