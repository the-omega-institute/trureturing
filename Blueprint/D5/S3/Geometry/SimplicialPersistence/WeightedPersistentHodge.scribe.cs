using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.SimplicialPersistence;

internal sealed class WeightedPersistentHodgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted persistent Hodge representatives for actual finite simplicial homology.",
        H("The weighted persistent Hodge theorem"),
        Blocks(
            Node("chains", "Chain", "Real chains on every actual face",
                "Let V be any finite linearly ordered vertex type, K and L any pre-abstract simplicial "
                + "complexes on V with K contained in L, and q any natural number. A q-face is an actual "
                + "face with q+1 vertices, ordered by the vertex order. The integer free face modules, "
                + "rank-signed deletion boundaries and their square-zero proof are those of "
                + "FiniteSimplicialSingularHomology. Chain is their scalar extension to Real on chains, "
                + "before taking homology. The original coordinate equivalence supplies the increasing-face "
                + "basis. In each degree coefficients identify the chains with all real functions on faces.",
                DescribeRole.Definition),
            Node("weights", "Weights", "All positive real face weights",
                "Weights supplies a strictly positive real number on every face of L in every natural "
                + "degree. Its restriction to K uses the identical underlying face. The inner product of "
                + "chains x,y in degree r is the sum of x(s)y(s)/w(r,s) over actual r-faces. The coefficient "
                + "metric of HomologyImage.WeightedModule gives exactly this inner product on both "
                + "complexes. No lower or uniform weight bound is assumed.", DescribeRole.Definition),
            Node("inclusion", "chainInclusion", "Actual zero extension and homology",
                "The integer inclusion sends each actual face generator of K to that same face generator "
                + "of L. Its coefficient retraction splits it, and signed face deletion commutes with it. "
                + "Scalar extension therefore gives injective real zero-extension maps in every degree "
                + "and a genuine map chainInclusion of the full real simplicial chain complexes. "
                + "The homology map is HomologicalComplex.homologyMap of this chain map. No identification "
                + "between scalar extension of homology and homology of scalar extension is assumed.",
                DescribeRole.Definition),
            Node("operator", "persistentLaplacian", "The restricted weighted operator",
                "In degree q let U be all chains c of degree q+1 in L whose ordinary boundary belongs "
                + "to the range of zero extension from degree q of K. U has the inherited weighted "
                + "inner product. Let T:U→Cq(K) be the unique restricted boundary satisfying i(Tc)=boundary(c). "
                + "Let D be the outgoing boundary on K, zero at q=0 and the ordinary signed boundary in "
                + "positive degrees. The operator is Delta = T T* + D* D. Its adjoints use these exact "
                + "weighted inner products. U includes all linear combinations with cancelling hidden "
                + "boundary, rather than only individually retained simplices.", DescribeRole.Definition),
            Node("equivalence", "persistentHodgeEquiv", "Harmonic chains and the actual image",
                "For every V, K, L, inclusion, positive weight family and natural degree specified above, "
                + "persistentHodgeEquiv is a real linear equivalence from ker(Delta) to the range of the "
                + "actual induced real simplicial homology map Hq(K)→Hq(L). Its construction uses the "
                + "harmonic orthogonal complement of cycles killed by L filling chains, followed by the "
                + "canonical comparison with actual chain-complex homology.", DescribeRole.Definition),
            Node("theorem", "weighted_persistent_hodge", "The complete weighted theorem",
                "For every finite linearly ordered V, every finite simplicial inclusion K contained in L, "
                + "every natural q, and every strictly positive real weight on every face of L in each "
                + "degree, both the L and restricted K inner products equal their coefficient sums "
                + "sum_s x(s)y(s)/w(r,s) in every degree r. For every harmonic q-chain h the equivalence "
                + "sends h to [i(q)(h)] in the actual homology of L. In particular the real finrank of "
                + "ker(Delta) equals the real finrank of the range of Hq(chainInclusion). Empty face "
                + "sets, all degrees above dimension, K=L, disconnected complexes, zero boundary ranks "
                + "and classes killed only by new filling chains in L are included. There is no "
                + "homology-vanishing, boundary-invertibility, lower-weight-bound or uniform-weight-bound "
                + "hypothesis. The nullity equality is Theorem 2.7 of Mémoli, Wan and Wang; the explicit "
                + "canonical representative equivalence is the chain-level interface established here, "
                + "rather than a verbatim quotation of that theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature("memoliwanwang2022persistentlaplacians"),
        Blocks(Paragraph(Text(prose))), role);
}
