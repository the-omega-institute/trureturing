using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class NeighborhoodIdealDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal.";
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Family => Fn(V("Branch"), Call("Set", V("Nat")));
    private static Formula Large => Grp(Seq(
        All("r", V("unitInterval")), All("V", Call("Set", V("unitInterval"))),
        V("V"), Sp, InMacro, Sp, Call("nhds", V("r")), Sp, Rightarrow, Sp,
        Neg, Call("InFiniteUnionIdeal", V("M"), Call("preimage", V("natValue"), V("V")))));
    private static Formula Existence => Disp(Seq(
        Ex("M", Family),
        Grp(Seq(All("x", V("Branch")), Call("natBranch", V("x")), Sp, Subseteq, Sp, Call("M", V("x")))),
        Sp, Land, Sp,
        Grp(Seq(All("x", V("Branch")), All("y", V("Branch")), V("x"), Sp, Neq, Sp, V("y"),
            Sp, Rightarrow, Sp, Call("Finite", Call("inter", Call("M", V("x")), Call("M", V("y")))))),
        Sp, Land, Sp, Call("MADFamily", Call("range", V("M"))), Sp, Land, Sp,
        Grp(Seq(All("x", V("Branch")), Call("ConvergesOn", V("natValue"), Call("M", V("x")), Call("limitValue", V("x"))))),
        Sp, Land, Sp, Large));
    private static Formula Threshold => Disp(Seq(
        All("M", Family), Large, Sp, Rightarrow, Sp, All("D", Call("Set", V("Nat"))),
        Call("LowerThird"), Sp, Subseteq, Sp, V("D"), Sp, Land, Sp,
        V("D"), Sp, Subseteq, Sp, Call("UpperTwoThirds"), Sp, Rightarrow, Sp,
        Call("Nonempty", Call("inter", Call("ColorSupport", V("M"), V("natValue"), V("D")),
            Call("ColorSupport", V("M"), V("natValue"), Call("compl", V("D")))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergent maximal families have large value neighborhoods and a common threshold color support.",
        H("Neighborhood ideal and common color support"),
        Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Paragraph(Text(
                "InFiniteUnionIdeal(M,E) means that E is contained in the union of finitely many actual M(x), together with a finite set. "
                + "ColorSupport(M,u,D) contains the r for which every neighborhood V of r has u-preimage(V) intersected with D outside this ideal. "
                + "LowerThird is {n : natValue(n) ≤ 1/3}; UpperTwoThirds is {n : natValue(n) < 2/3}. "
                + "All inequalities concern the real coercion of the unit-interval value. nhds, preimage, inter and compl denote literal Lean neighborhoods and set operations.")),
            Describe.Lean(
                DescribeId.Create("exists-mad-no-small-neighborhood"),
                DeclarationHandle.Create(Owner + "exists_mad_with_no_small_neighborhood"),
                H("Actual maximal family with large value neighborhoods"),
                StatementSource.FromAuthor(Existence), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing branch-labeled convergent maximal family is retained in full. "
                    + "Every value fiber has continuum many branch labels, so a label can be chosen outside any given finite family. "
                    + "Its infinite member has only finitely many points outside the value neighborhood and only finitely many intersections with the proposed cover members. "
                    + "A finite cover plus a finite exceptional set would make that member finite, a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-common-color-support"),
                DeclarationHandle.Create(Owner + "threshold_common_color_support"),
                H("Exact thresholds force a common color support"),
                StatementSource.FromAuthor(Threshold), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The generated ideal is closed under taking subsets and finite unions. Each color support is closed: a small neighborhood at r contains an open smaller neighborhood witnessing smallness at every point in it. "
                        + "The two supports cover the interval, since two small colored neighborhoods would make their intersection a small uncolored neighborhood.")),
                    Paragraph(Text(
                        "The lower threshold excludes zero from the complement-color support, and the upper threshold excludes one from the D-color support. "
                        + "Connectedness of unitInterval therefore gives a point in both closed supports. "
                        + "The partitioner diagonal, uncountability and continuum size of both limit-color fibers, separator elimination, compact counterexample, and Ref classification remain unproved."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily"))]));
}
