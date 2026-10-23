using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class TaggedCompactSpaceDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Statement => Disp(Seq(
        All("A", Call("Set", Call("Set", V("Nat")))),
        All("u", Fn(V("Nat"), V("unitInterval"))),
        All("ell", Fn(V("A"), V("unitInterval"))),
        Call("PairwiseFiniteIntersections", V("A")), Sp, Land, Sp,
        Grp(Seq(All("a", V("A")), Call("ConvergesOn", V("u"), Call("val", V("a")), Call("ell", V("a"))))),
        Sp, Rightarrow, Sp,
        Call("IsClosed", Call("literalSpace", V("A"), V("u"), V("ell"))), Sp, Land, Sp,
        Call("IsCompact", Call("literalSpace", V("A"), V("u"), V("ell"))), Sp, Land, Sp,
        Call("Continuous", Call("projection", V("A"), V("u"), V("ell"))), Sp, Land, Sp,
        Call("IsOpenMap", Call("projection", V("A"), V("u"), V("ell"))), Sp, Land, Sp,
        Call("Surjective", Call("projection", V("A"), V("u"), V("ell"))), Sp, Land, Sp,
        Grp(Seq(All("a", V("A")), Call("Continuous", Call("sectionLift", V("A"), V("u"), V("ell"), V("a"))))),
        Sp, Land, Sp,
        Grp(Seq(All("a", V("A")), Call("IsClopen", Call("range", Call("sectionLift", V("A"), V("u"), V("ell"), V("a"))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal tagged compact product and its open projection.",
        H("Coherent tags produce a compact open surjection"),
        Blocks(
            Paragraph(Text("A is a set of distinct actual subsets of Nat whose distinct members have finite intersections; infinity of each member is not required for this construction. Its subtype, rather than repeated branch labels, supplies the family coordinates. The ambient space is OnePoint Nat times unitInterval times Bool^(A + Nat). The literal space retains the entire zero-vector interval core, the actual d_n with all membership and singleton coordinates, every finite nonmember family tag and the tagged limit point for every actual member.")),
            Paragraph(Text("The information audit remains unfinished: the source-owner mirror checks the exact generic source telescope. A faithful whole-source variation arena and raw source occurrence reconstruction/sourceSelection remain absent; the same-target issue is linked in the final delivery. This is not a validated four-slot registration.")),
            Describe.Lean(
                DescribeId.Create("literal-closed-compact-open-surjection"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace.literal_closed_compact_open_surjection"),
                H("Closed coordinate shell, continuous sections and clopen section ranges"),
                StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a in A, its section agrees with d_n when n lies in a, and otherwise uses its own tagged point at the base n. The value coordinate converges by the assumed finite-exception convergence on a. Almost-disjoint intersections and singleton coordinates make every other tag coordinate eventually constant. The section is continuous into the actual product.")),
                    Paragraph(Text("Each family coordinate piece is a continuous compact section range; each natural-number coordinate piece is a singleton. If any tag is true at a point in one coordinate piece, that point belongs to the corresponding piece. Consequently the literal union is exactly the intersection, over every coordinate gamma, of the closed false-coordinate slice union its compact coordinate piece. This uses arbitrary closed intersections and does not assume countability, sequentiality, CH or regularity of continuum.")),
                    Paragraph(Text("At infinity every point lies on a continuous core or family section. At a finite isolated base point, overwrite a core section to pass through the selected fiber point. Mathlib IsOpenMap.of_sections proves that the actual projection is open. The core also proves it is onto. Each family section range equals its own true-coordinate slice and is clopen.")),
                    Paragraph(Text("The result works for an arbitrary actual family with pairwise finite intersections with the stated convergence, including an empty family, and exposes the natural points, sections and projection for the subsequent closed-piece partitioner argument. It does not by itself prove the finite-refinement obstruction, the base classification or the original Peng dynamical question."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/ConvergentBranches"))]));
}
