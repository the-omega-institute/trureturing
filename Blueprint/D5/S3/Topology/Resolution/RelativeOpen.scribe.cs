using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Resolution;

internal sealed class RelativeOpenDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Resolution/RelativeOpen.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, string type) =>
        Seq(Grp(), OpenBracket, Call(name, V(type)), CloseBracket, Sp);
    private static Formula Compose => Call("compose", V("p"), V("r"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("B", Seq(V("Type"), Underscore, Grp(V("uB")))),
            All("T", Seq(V("Type"), Underscore, Grp(V("uT")))),
            All("K", Seq(V("Type"), Underscore, Grp(V("uK"))))),
        Seq(Inst("TopologicalSpace", "B"), Inst("CompactSpace", "B"),
            Inst("TTwoSpace", "B"), Inst("TotallyDisconnectedSpace", "B")),
        Seq(Inst("TopologicalSpace", "T"), Inst("CompactSpace", "T"), Inst("TTwoSpace", "T"),
            Inst("MetricSpace", "K"), Inst("CompactSpace", "K")),
        Seq(All("p", Fn(V("T"), V("B"))), All("u", Fn(V("T"), V("K")))),
        Seq(Call("Continuous", V("p")), Sp, Land, Sp, Call("IsOpenMap", V("p")),
            Sp, Land, Sp, Call("Surjective", V("p")), Sp, Land, Sp, Call("Continuous", V("u")),
            Sp, Land, Sp, Call("IsEmbedding", Call("pairmap", V("p"), V("u"))), Sp, Rightarrow),
        Seq(Exists, Sp, V("Z"), Colon, Sp, V("Type"), Underscore, Grp(V("uB")), Comma, Sp,
            Exists, Sp, V("tZ"), Colon, Sp, Call("TopologicalSpace", V("Z")), Comma),
        Seq(Call("CompactSpace", V("Z")), Sp, Land, Sp, Call("TTwoSpace", V("Z")),
            Sp, Land, Sp, Call("TotallyDisconnectedSpace", V("Z")), Sp, Land),
        Seq(Exists, Sp, V("r"), Colon, Sp, Fn(V("Z"), V("T")), Comma, Sp,
            Call("Continuous", V("r")), Sp, Land, Sp, Call("Surjective", V("r")), Sp, Land),
        Seq(Call("IsOpenMap", Compose), Sp, Land, Sp, Call("Surjective", Compose), Sp, Land,
            Grp(Seq(Call("MetrizableSpace", V("B")), Sp, Rightarrow, Sp,
                Call("MetrizableSpace", V("Z")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An open compact Hausdorff map with a compact metrizable kernel admits a zero-dimensional resolution preserving openness over an arbitrary compact zero-dimensional base.",
        H("Relative open-preserving zero-dimensional resolution"),
        Blocks(
            Paragraph(Text(
                "The universe levels uB, uT and uK are independent. B is compact Hausdorff and totally disconnected, "
                + "T is compact Hausdorff, and K is compact metric. The map p is continuous, open and surjective. "
                + "The continuous map u separates points within fibers: pairmap(p,u) sends t to (p(t),u(t)) and is a topological embedding. "
                + "This is the relative metrizable-kernel hypothesis. No metric or countable basis on B, and no metric on T, is assumed.")),
            Describe.Lean(
                DescribeId.Create("exists-relative-open-resolution"),
                DeclarationHandle.Create(Owner + "exists_relative_open_resolution"),
                H("Full relative resolution"),
                StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All properties of Z and r use the returned topology tZ. compose(p,r) denotes p after r. "
                        + "The same constructed Z is metrizable whenever B is metrizable. The theorem supplies an actual type and map, "
                        + "rather than assuming a package of sections, paths or open projections.")),
                    Paragraph(Text(
                        "Let F be the literal range of pairmap(p,u). Compactness and the Hausdorff product make F closed. "
                        + "Define Phi(b) to be exactly the set of k with (b,k) in F. Surjectivity of p makes each fiber nonempty; "
                        + "its closedness is the preimage of F under k mapped to (b,k). For every open U in K the hitting set "
                        + "{b : Phi(b) intersects U} equals p applied to the inverse image of U under u. It is open. "
                        + "Compact K supplies completeness by complete_of_compact. The classical prescribed-point selection theorem "
                        + "CompactZeroDimensional.exists_continuous_selection_through therefore gives a continuous K-valued fiber selector through every t.")),
                    Paragraph(Text(
                        "Put epsilon(n)=(1/2)^n. For each t the distance-open set W(t) consists of x in T with "
                        + "dist(u(x),v(t)(p(x))) less than epsilon(n), where v(t) is the selector through t. These W(t) cover all of T. "
                        + "A finite subcover of compact T, reindexed by I(n)=Fin(N(n)), gives finitely many global selectors v(n,i). "
                        + "For every actual fiber point k over b, some v(n,i)(b) is within epsilon(n) of k. "
                        + "The finite cover is taken on all T, rather than on a single fiber or only on B.")),
                    Paragraph(Text(
                        "The distance between v(n,i) and v(n+1,j) is continuous on B. Interpolate its closed band "
                        + "distance at most epsilon(n)+epsilon(n+1) inside its open band distance less than "
                        + "2 epsilon(n)+epsilon(n+1), using exists_clopen_of_closed_subset_open. Call the resulting clopen set A(n,i,j). "
                        + "At every base b, every vertex i has a successor: apply the next net to the fiber member v(n,i)(b). "
                        + "Separately, for every prescribed k in Phi(b), choose net indices at all levels for that same k. "
                        + "The triangle inequality puts all consecutive pairs in their lower distance bands. This gives a full allowed path approximating k.")),
                    Paragraph(Text(
                        "Z is the closed subtype of B times the dependent product of I(n), containing exactly pairs (b,a) "
                        + "with b in A(n,a(n),a(n+1)) for every n. Each transition predicate is a finite union of clopen slices, "
                        + "and their intersection is closed. Compactness, Hausdorffness and total disconnectedness pass from the product to Z. "
                        + "The dynamic map z mapped to v(n,z.indices(n))(z.base) is continuous by continuous_prod_of_discrete_right. "
                        + "Its bounded continuous maps have uniform increments at most (5/2)epsilon(n). The geometric Cauchy theorem and "
                        + "completeness give a continuous uniform limit k, with tail at most 5 epsilon(n).")),
                    Paragraph(Text(
                        "For every path the pairs (z.base,v(n,z.indices(n))(z.base)) belong to F. Their limit (z.base,k(z)) "
                        + "stays in F by closedness, without any metric on B. Apply the inverse of IsEmbedding.toHomeomorph to return to the original T; "
                        + "this defines continuous r and proves p after r equals the base projection. For each t, its specific approximating path "
                        + "has limit u(t): the uniform tail and net error bound its distance by 6 epsilon(n), which tends to zero. "
                        + "The range homeomorphism then gives r(z)=t literally. Both r and p after r are surjective.")),
                    Paragraph(Text(
                        "For an open V in B and a prefix x of length N, the base-projection image of the corresponding cylinder in Z "
                        + "is exactly V intersected with A(n,x(n),x(n+1)) for n in Finset.range(N-1). "
                        + "The reverse inclusion extends the final prescribed vertex at that same base, using dependent Nat recursion and seriality. "
                        + "For length zero there are no prescribed transitions: start at x(0) and construct a path at that base. "
                        + "Thus every cylinder image is open. PiNat.isTopologicalBasis_cylinders, the product and subtype bases, "
                        + "and IsTopologicalBasis.isOpenMap_iff prove openness for arbitrary open subsets of Z.")),
                    Paragraph(Text(
                        "No Nonempty instance is assumed on B, T or K. Empty T can produce empty finite covers, and all constructions are empty functions "
                        + "where required. If B has a point, surjectivity of p supplies a point of T and then of K; no arbitrary K point is used. "
                        + "For the optional clause only, PiNat.metricSpace gives the dependent Nat product its compatible discrete-product metric. "
                        + "Metrizability of B then passes through the product and subtype to this same Z.")),
                    Paragraph(Text(
                        "The selection input is Michael's classical zero-dimensional selection principle, with the attribution and inspected scope "
                        + "in Library/Topology/valov2008milyutinmaps.md. The relative construction and its applicability are explained in "
                        + "Library/Topology/project2026relativeopenresolution.md. This theorem concerns a metrizable relative kernel; "
                        + "it does not resolve unrestricted nonmetric open-map resolution or Peng Questions 5.1 and 5.2."))),
                DescribeRole.Theorem))));
}
