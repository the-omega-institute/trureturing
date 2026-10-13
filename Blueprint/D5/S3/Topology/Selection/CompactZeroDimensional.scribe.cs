using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Selection;

internal sealed class CompactZeroDimensionalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Selection/CompactZeroDimensional.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Fn(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, Formula type) =>
        Seq(Grp(), OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula At(Formula f, string x) => Seq(f, Open, V(x), Close);
    private static Formula FiberMember(string x, Formula f) =>
        Seq(At(f, x), Sp, InMacro, Sp, At(Phi, x));
    private static Formula MemberLaw(Formula f) =>
        Seq(All("b", V("B")), FiberMember("b", f));
    private static Formula[] Assumptions() => [
        Seq(All("B", Seq(V("Type"), Underscore, Grp(V("u")))),
            All("K", Seq(V("Type"), Underscore, Grp(V("v"))))),
        Seq(Inst("TopologicalSpace", V("B")), Inst("CompactSpace", V("B")),
            Inst("TTwoSpace", V("B")), Inst("TotallyDisconnectedSpace", V("B"))),
        Seq(Inst("MetricSpace", V("K")), Inst("CompleteSpace", V("K"))),
        Seq(Forall, Sp, Phi, Colon, Sp, Fn(V("B"), Call("Set", V("K"))), Comma, Sp),
        Seq(Grp(Seq(All("b", V("B")), Call("Nonempty", At(Phi, "b")))), Sp, Rightarrow),
        Seq(Grp(Seq(All("b", V("B")), Call("IsClosed", At(Phi, "b")))), Sp, Rightarrow),
        Seq(Grp(Seq(All("U", Call("Set", V("K"))), Call("IsOpen", V("U")),
            Sp, Rightarrow, Sp, Call("IsOpen", Call("Hit", Phi, V("U"))))), Sp, Rightarrow)
    ];
    private static Formula Conclusion(bool through) =>
        Seq(Exists, Sp, V("f"), Colon, Sp, Fn(V("B"), V("K")), Comma, Sp,
            Call("Continuous", V("f")), Sp, Land, Sp, Grp(MemberLaw(V("f"))),
            through ? Seq(Sp, Land, Sp, At(V("f"), "bzero"), Sp, Eq, Sp, V("kzero")) : Seq());
    private static Formula Statement(bool through) => Disp(new Formula.Aligned(
        through ? [.. Assumptions(),
            Seq(All("bzero", V("B")), All("kzero", V("K"))),
            Seq(V("kzero"), Sp, InMacro, Sp, At(Phi, "bzero"), Sp, Rightarrow),
            Conclusion(true)] : [.. Assumptions(), Conclusion(false)]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed nonempty lower semicontinuous fibers over compact zero-dimensional spaces admit continuous selections, including prescribed fiber points.",
        H("Compact zero-dimensional continuous selection"),
        Blocks(
            Paragraph(Text(
                "The universe levels u and v are independent. B is an arbitrary compact Hausdorff totally disconnected topological space, "
                + "and K is a complete metric space. Phi maps B to subsets of K. "
                + "Hit(Phi,U) denotes exactly the set of b for which Phi(b) intersects U nontrivially. "
                + "Nonempty(Phi(b)) means nonemptiness of that subset, rather than a carrier typeclass. "
                + "The open-hit condition is the literal lower semicontinuity hypothesis, equivalent to Mathlib's LowerHemicontinuous.")),
            Describe.Lean(
                DescribeId.Create("exists-continuous-selection"),
                DeclarationHandle.Create(Owner + "exists_continuous_selection"),
                H("Continuous fiber-member selection"),
                StatementSource.FromAuthor(Statement(false)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every multifunction with nonempty closed fibers and open hitting sets for all open target sets, "
                        + "there exists a continuous function f from B to K with f(b) in Phi(b) at every b. "
                        + "B need not be metrizable, first countable, second countable, separable, or equipped with a countable basis. "
                        + "K need not be compact, separable, convex, or linear.")),
                    Paragraph(Text(
                        "Choose fiber points to form an open cover by fiber hitting balls. "
                        + "TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover refines the cover into finitely many disjoint clopen cells. "
                        + "The value assigned to each cell is the center belonging to the cover member that contains the cell. "
                        + "This gives a finite locally constant first approximation with fiber error less than one.")),
                    Paragraph(Text(
                        "At stage n put epsilon(n)=(1/2)^n. Intersect the open equality fiber of the old locally constant map "
                        + "with a fiber hitting ball centered at an actual nearby fiber point. A finite clopen refinement gives the next approximation, "
                        + "with fiber error less than epsilon(n+1) and pointwise increment at most epsilon(n). "
                        + "These inequalities give the same bound in the uniform metric on bounded continuous functions. "
                        + "Mathlib's geometric Cauchy theorem and completeness supply a bounded continuous limit with uniform tail bound 2 epsilon(n). "
                        + "A fiber point within epsilon(n) of the nth approximation is within 3 epsilon(n) of the limit; "
                        + "closedness of each exact fiber puts the limit in that fiber.")),
                    Paragraph(Text(
                        "Neither B nor K has a Nonempty assumption in the theorem. If B is empty, the cell-index function and all subsequent functions are empty functions, "
                        + "even when K is empty. No arbitrary target inhabitant is chosen. If B has a point, the nonempty fiber at that point already supplies a target point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-continuous-selection-through"),
                DeclarationHandle.Create(Owner + "exists_continuous_selection_through"),
                H("Selection through a prescribed fiber point"),
                StatementSource.FromAuthor(Statement(true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every bzero in B and every kzero in Phi(bzero), one may also require f(bzero)=kzero. "
                        + "Replace only the fiber at bzero by the singleton containing kzero. All fibers stay nonempty and closed. "
                        + "For an open U containing kzero, its hitting set is unchanged. For U excluding kzero, its hitting set is the old open hitting set "
                        + "minus the closed singleton containing bzero. Thus the modified multifunction still satisfies the literal open-hit condition. "
                        + "The full selection theorem applied to it gives both membership in the original fibers and the prescribed equality.")),
                    Paragraph(Text(
                        "This is the compact-domain form of Michael's classical zero-dimensional selection principle. "
                        + "Valov's arXiv:0801.1721v2 uses the classical principle in Lemma 2.2 and cites Michael's Selected selection theorems; "
                        + "the consulted source and its scope are recorded in Library/Topology/valov2008milyutinmaps.md. "
                        + "No theorem number from the uninspected original Michael article or from Semenov and Shchepin's article is asserted here. "
                        + "The result supplies prescribed sections for a future open-map resolution argument under a metrizable-kernel hypothesis. "
                        + "That resolution is not asserted by these selection statements, and neither Peng Question 5.1 nor Question 5.2 is resolved here."))),
                DescribeRole.Theorem))));
}
