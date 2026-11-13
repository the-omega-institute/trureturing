using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ExclusionIncidenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ExclusionIncidence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper association of the entire original exclusion fibers at pure limiting labels.",
        H("Original exclusion incidence"), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed vector space. C is the original pointed cone, closed and generating, and the original real linear unit u is strictly positive on nonzero cone vectors. K is the entire base C intersect {u=1}, P is all of ext(K) with its actual subspace topology, proper effects are all real linear f with 0<=f<=u on C, and D_p is the entire original exclusion set. The hypotheses do not supply a physical inner product, compactness or closedness of P, label injectivity, Pair, least effects, spectrality or a Jordan representation.")),
            Describe.Lean(DescribeId.Create("exclusion-upper-limit"),
                DeclarationHandle.Create(Owner + "exclusion_upper_limit"),
                H("Limits of actual original exclusions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p, every sequence pn of original pure labels converging to p in P, every sequence yn in V converging to y, if yn(n) belongs to the entire D_pn(n) for every n, then y belongs to the entire D_p. There is no ball assumption in this prerequisite of IX118.3. It also applies to the nonzero original EB3 domain.")),
                    Paragraph(Text("Choose an actual full-interval proper confirmer f_n witnessing yn(n) in D_pn(n). Regard it as a continuous linear map in the unchanged original norm; finite dimensionality makes this representation exact. The unchanged effects_compact proof from ContinuousFrameSum supplies a convergent subsequence in the entire original effect interval. Joint continuous evaluation at the same subsequence of labels and states gives e(p)=1 and e(y)=0. Closedness of the original compact base gives y in K. The same e is therefore an actual witness for y in D_p. This pointwise argument needs no continuously selected confirmer and no pure-limit closure assumption. exclusion_upper_eventually consumes this statement on its live subsequence path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exclusion-upper-eventually"),
                DeclarationHandle.Create(Owner + "exclusion_upper_eventually"),
                H("Uniform upper approximation of entire fibers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p, every pn tending to p in the actual P, and every positive real epsilon, eventually for every y in the entire D_pn(n) there is z in the entire D_p with original-norm distance dist(y,z)<epsilon. The quantifiers include every mixed state of every exclusion fiber. Compactness of K is derived from the closed cone and strictly positive original unit; it is not an extra input.")),
                    Paragraph(Text("If uniform upper approximation fails, extract a strictly increasing sequence of bad indices and one actual bad exclusion state per index. Compactness of K supplies a second subsequence converging to z. The same composed label subsequence still tends to the original pure p. exclusion_upper_limit places z in D_p, contradicting the positive lower bound on the distances of all chosen bad states to every point of D_p. This is the upper half of the whole-fiber Hausdorff argument in IX118.3, not that theorem's equivalence."))),
                DescribeRole.Theorem),
            Paragraph(Text("The remaining IX118.2 statement concerns every sequence of full affine three-balls F_n in a finite dimensional Euclidean ambient converging in Hausdorff distance to another full affine three-ball F. Their boundaries are intrinsic to their moving affine hulls, and semiaxes may vary arbitrarily; no continuous chart or common physical inner product is supplied. The full-rank limit is essential: diag(1,1,1/n) applied to the unit three-ball converges to a disk, while the images of its unit spheres converge to the whole disk, not the disk's relative boundary. The points (0,0,1) on the source spheres map to (0,0,1/n) and tend to the relative interior center. This is a paper counterexample to dropping rank, not an EB3 countermodel.")),
            Paragraph(Text("The whole IX118.3 target remains the equivalence of original edge lifting (O), openness of pi1 on the actual incidence I={(p,q) in P squared : q in P intersect D_p}, and Hausdorff continuity of p mapped to the entire D_p. (O) quantifies over every actual edge (p,q) and every sequence pn tending to p, and requires a sequence qn tending to q with (pn(n),qn(n)) in I for every n. Its consequences are Hausdorff continuity of the whole P intersect D_p and openness of pi2 through actual zero-symmetry swap. Still required are the original full-ball diameter-endpoint decomposition, simultaneous lifts on the same label sequence, the compact finite-net lower estimate, moving-rank-three intrinsic-boundary convergence, and the exact original-domain assembly. Arbitrary-norm to auxiliary-Euclidean transport and metric correspondence must be proved before using the geometric lemma on original V. Neither this upper estimate nor generic projection/lower-hemicontinuity packaging supplies those missing clauses. No part of this module asserts the full equivalence or closes its atom."))
        )));
}
