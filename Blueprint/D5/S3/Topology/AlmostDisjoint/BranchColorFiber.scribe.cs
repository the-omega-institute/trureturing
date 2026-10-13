using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class BranchColorFiberDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Statement => Disp(Seq(
        All("M", Fn(V("Branch"), Call("Set", V("Nat")))),
        Grp(Seq(All("x", V("Branch")), Call("natBranch", V("x")), Sp, Subseteq, Sp, Call("M", V("x")))),
        Sp, Land, Sp, Call("MADFamily", Call("range", V("M"))), Sp, Land, Sp,
        Grp(Seq(All("x", V("Branch")), Call("ConvergesOn", V("natValue"), Call("M", V("x")), Call("limitValue", V("x"))))),
        Sp, Rightarrow, Sp, All("D", Call("Set", V("Nat"))),
        Call("Partitions", V("M"), V("D")), Sp, Rightarrow, Sp,
        All("r", V("unitInterval")), V("r"), Sp, InMacro, Sp,
        Call("ColorSupport", V("M"), V("natValue"), V("D")), Sp, Rightarrow, Sp,
        Call("mk", Call("Fiber", V("M"), V("D"), V("r"))), Sp, Eq, Sp, V("continuum")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tree-prefix coding upgrades partitioner color fibers from uncountable to continuum.",
        H("Closed branch-tail slices and continuum color fibers"),
        Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Paragraph(Text(
                "Branch is the actual four-letter Cantor space Nat → (Bool × Bool). "
                + "prefixNat(x,k) is wordEquivNat(wordPrefix(x,k)), and natBranch(x) is the set of these actual natural-number prefixes. "
                + "Fiber(M,D,r) denotes the subtype {x : Branch : limitValue(x)=r and M(x) minus D is finite}. "
                + "The theorem requires the same M to contain each corresponding natBranch, be unrestricted maximal almost disjoint, "
                + "and converge along M(x) to the actual limitValue(x). These correspondences are explicit hypotheses.")),
            Describe.Lean(
                DescribeId.Create("partitioner-fiber-continuum"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/BranchColorFiber.partitioner_fiber_continuum"),
                H("Every supported eventual-color fiber has continuum cardinality"),
                StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The enlarged maximal family need not depend continuously or Borel-measurably on its label. "
                        + "The partitioner hypothesis nevertheless recovers an exact finite-prefix description of its color: "
                        + "M(x) minus D is finite if and only if there exists m such that prefixNat(x,k) belongs to D for all k≥m. "
                        + "The forward implication bounds lengths of the finitely many exceptional words. "
                        + "In the reverse implication, the opposite partitioner color would make the infinite original branch finite, "
                        + "using its containment in M(x). Thus the color test is pulled back to the original tree without asserting M(x)=natBranch(x).")),
                    Paragraph(Text(
                        "TailSlice(D,r,m) is the closed limit fiber intersected with all prefix-color conditions for k≥m. "
                        + "Each prefix-color condition is closed because a finite-coordinate cylinder fixes that literal prefix; "
                        + "the limit fiber is closed by the previously proved continuity of limitValue. "
                        + "The eventual-color fiber is exactly the countable union of these actual closed slices. "
                        + "This proves the required F-sigma regularity rather than assuming that an arbitrary uncountable maximal-family label set is Borel.")),
                    Paragraph(Text(
                        "The maximality diagonal makes this fiber uncountable, so one closed slice is uncountable. "
                        + "Mathlib's IsClosed.exists_nat_bool_injection_of_not_countable supplies a genuine Cantor injection into that slice. "
                        + "Its cardinal lower bound is continuum, while the upper bound comes from the already checked continuum cardinality of the actual limitValue fiber. "
                        + "No CH or regularity of continuum is used. Separator elimination and the compact open-map counterexample remain outstanding. "
                        + "The Reg mirror checks the exact source telescope; faithful four-slot reconstruction evidence is unfinished."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal"))]));
}
