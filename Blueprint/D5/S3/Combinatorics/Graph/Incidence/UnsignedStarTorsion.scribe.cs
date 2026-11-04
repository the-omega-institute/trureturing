using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class UnsignedStarTorsionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact unsigned integer star lattices: common remainders, order-two localization, and original-source coefficient-one recovery.",
        H("Unsigned Star Lattices and Sparse Integral Recovery"),
        Blocks(
            Paragraph(Text("The vertex type V indexes rows and X indexes individually identified original edges. "
                + "An Edges value gives distinct endpoints left(i), right(i). Parallel original coordinates remain distinct. "
                + "The exact integer linear map is f(a)(i)=a(left(i))+a(right(i)). Its image is not replaced by its saturation. "
                + "graphAfterDeleting D first removes exactly the original indices in D, then uses existence of a remaining "
                + "edge as the underlying simple adjacency. Thus deletion and support cardinalities never conflate parallel indices.")),
            Describe.Lean(DescribeId.Create("integer-injectivity"),
                DeclarationHandle.Create(Prefix + "starMap_injective"),
                H("Consumed Integer Injectivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected nonbipartite original graph, the exact integer star map is injective. "
                    + "Apply the existing private nonbipartite_potential proof to the difference of two potentials with equal images. "
                    + "Its constant has twice its value equal to zero, so it vanishes over the integers. "
                    + "This consumed corollary supplies injectivity to UnsignedStarFixedCokernel; it is a consumed helper, "
                    + "not a new generality claim or a new proof of the private potential theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bipartite-integral-recovery"),
                DeclarationHandle.Create(Prefix + "integral_of_bipartite"),
                H("Signed Root Normalization in a Bipartite Graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected bipartite original graph, k>0 and actual integer k*z=f(a), "
                    + "there exists actual integer b with f(b)=z. Choose the two colors from bipartiteness and "
                    + "write e(v)=1 or -1 accordingly. For a root r, subtract e(v)*e(r)*a(r) from each a(v). "
                    + "This is a genuine integer kernel of the star map and makes the root zero. Walk propagation "
                    + "then makes every normalized coefficient zero modulo k. Only after proving divisibility "
                    + "do we divide and cancel k in the ambient integer coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("remainders"),
                DeclarationHandle.Create(Prefix + "potential_remainders"),
                H("Integer Potential Remainders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any connected nonbipartite original graph, positive natural k, integer vectors z on X "
                    + "and a on V satisfying k*z(i)=f(a)(i) for every original i, there exists an integer r with "
                    + "0<=r<k, either r=0 or 2*r=k, and a(v) modulo k equals r for every vertex. "
                    + "Walk induction propagates residues as c or -c in ZMod k. If these differ they define a bipartition, "
                    + "contradicting nonbipartiteness. Integer remainder bounds then prove the two cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("torsion-alternative"),
                DeclarationHandle.Create(Prefix + "integer_potential_alternative"),
                H("The Exact Integral or Component-Total Alternative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same hypotheses, either z=f(b) for actual integer b, or k is even, "
                    + "every actual a(v) is nonzero, and actual integer b satisfies z(i)=f(b)(i)+1 and "
                    + "f(2*b+1)(i)=2*z(i). In the second case z is not in the image and the graph after deleting "
                    + "support(z) is bipartite. The full component total is not an integer star combination: "
                    + "such a combination would give a potential 2*b-1 with opposite adjacent values, forcing an integer half. "
                    + "Thus the second case is an actual nonzero order-two class of the exact quotient. No quotient cancellation is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-recovery"),
                DeclarationHandle.Create(Prefix + "integral_of_support_nonbipartite"),
                H("Coefficient One from Nonbipartiteness after Support Deletion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected original graph and actual k*z=f(a), k>0, if deletion of "
                    + "the original support of z leaves a nonbipartite graph, there exists integer b with f(b)=z. "
                    + "In the half case, all a(v) are nonzero and each undeleted edge has the exact equation a(u)+a(v)=0. "
                    + "Positive and negative potentials therefore color the entire deleted graph, including all pieces "
                    + "created by deletion. Connectedness after deletion is not a premise. In the zero case divisibility "
                    + "is proved before division, and k is cancelled only in the ambient integer coordinate group."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-source-coefficients"),
                DeclarationHandle.Create(Prefix + "source_coefficients_of_sparse_multiple"),
                H("Actual Original-Source Integer Coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V,X,H be finite, and fix q. Assume the original graph is connected and every "
                    + "deletion of at most q original indexed edges leaves a nonbipartite graph. Source rows rows(T) "
                    + "are integer vectors on X. Explicit integer d(T,v) give f(d(T))=rows(T), and explicit c(v,T) "
                    + "give starRow(v)(i)=sum_T c(v,T)*rows(T)(i). For any original z with support size at most q, "
                    + "positive k, and actual h(T) with k*z(i)=sum_T h(T)*rows(T)(i), the theorem returns integer b "
                    + "with f(b)=z and z(i)=sum_T (sum_v b(v)*c(v,T))*rows(T)(i). "
                    + "It first constructs a(v)=sum_T h(T)*d(T,v) and applies the new integral recovery. "
                    + "Both directions of the source lattice identification are explicit, and all original source rows "
                    + "participate; larger Boolean rows are not omitted. The left-hand coefficient is exactly one."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the original unit e_i or original difference e_i-e_j, the transient exact application "
                + "uses q=2 on the literal X coordinates and the displayed original-H coefficient formula. "
                + "No support-two bound is asserted after partial pivot maps. The connected original model is the retained "
                + "scope; componentwise classification, unrestricted exact integral full-blocker, unrestricted Good and AM "
                + "remain open. The supplied finite-free/PID and IntegerStrongOrdering chain is not reproved or retained as a wrapper.")),
            Paragraph(Text("Attribution: formalization of the caller-supplied completed argument, Exact Private Pivots, "
                + "Original Primitive Torsion, and a Mixed Cyclic Core, Sections 6-7, SHA256 "
                + "f776b4a6cba72126daf67658b7c846279a39d61cbdd41f6e2cfdd400f8e487f8. "
                + "Its independent native review is mathematical guidance, not kernel evidence or official acceptance. "
                + "Existing signed-incidence total unimodularity concerns endpoint differences and does not supply this "
                + "unsigned nonbipartite inference. No literature-priority or unrestricted Good claim is made.")))));

}
