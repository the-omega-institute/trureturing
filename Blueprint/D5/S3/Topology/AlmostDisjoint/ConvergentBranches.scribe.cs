using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class ConvergentBranchesDocument : IScribeDocumentDefinition
{
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula BranchStatement => Disp(Seq(
        All("n", V("Nat")),
        Grp(Seq(All("x", V("Branch")), Equal(Call("wordValue", Call("wordPrefix", V("x"), V("n"))), Call("finiteDyadicSum", V("x"), V("n"))))),
        Sp, Land, Sp, Grp(Seq(All("x", V("Branch")), Call("Infinite", Call("branchSet", V("x"))))),
        Sp, Land, Sp, Grp(Seq(All("x", V("Branch")), All("y", V("Branch")), V("x"), Sp, Neq, Sp, V("y"), Sp, Rightarrow, Sp,
            Call("Finite", Call("inter", Call("branchSet", V("x")), Call("branchSet", V("y")))))),
        Sp, Land, Sp, Grp(Seq(All("x", V("Branch")), Call("ConvergesOn", V("wordValue"), Call("branchSet", V("x")), Call("limitValue", V("x"))))),
        Sp, Land, Sp, Call("Continuous", V("limitValue")), Sp, Land, Sp, Call("Surjective", V("limitValue")),
        Sp, Land, Sp, All("r", V("unitInterval")), Equal(Call("cardinal", Call("fiber", V("limitValue"), V("r"))), V("continuum"))));
    private static Formula RangeStatement => Disp(Seq(
        All("alpha", V("Type")), All("Y", V("Type")), All("topology", Call("TopologicalSpace", V("Y"))),
        All("f", Fn(V("Nat"), V("alpha"))), All("u", Fn(V("alpha"), V("Y"))), All("r", V("Y")),
        Call("Tendsto", Call("compose", V("u"), V("f")), V("atTop"), Call("nhds", V("r"))),
        Sp, Rightarrow, Sp, Call("ConvergesOn", V("u"), Call("range", V("f")), V("r"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-letter convergent branches.", H("Four-letter convergent branches"), Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Describe.Lean(
                DescribeId.Create("branch-system"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/ConvergentBranches.branch_system"),
                H("The actual four-letter branch system"), StatementSource.FromAuthor(BranchStatement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Word is a nonempty list over Bool times Bool. PiNat.res stores reversed prefixes; wordBits reverses the list before its chronological binary interpretation and pads with false. finiteDyadicSum(x,n) denotes the sum over i less than n+1 of the first chronological bit, interpreted in Fin 2, divided by 2 to the i+1. The dyadic identity is an actual finite sum, and the OfDigits tail estimate bounds the prefix error by the inverse of 2 to the prefix length. Branch sets are infinite, distinct branches meet finitely, and their values converge in the finite-exception sense. The binary first-coordinate map is continuous and onto unitInterval; each fiber has cardinal continuum because its second binary coordinate is free."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("converges-on-range"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/ConvergentBranches.convergesOn_range"),
                H("Convergent sequences give finite-exception convergence on their ranges"), StatementSource.FromAuthor(RangeStatement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary carriers and an arbitrary target topology, a sequence converging atTop has only finitely many range elements outside any neighborhood of its limit. Repeated values are allowed. This lemma is consumed by the actual branch convergence and compact-interval subsequence construction."))), DescribeRole.Theorem))));
}
