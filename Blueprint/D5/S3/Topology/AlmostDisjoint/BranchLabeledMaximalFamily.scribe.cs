using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class BranchLabeledMaximalFamilyDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Statement => Disp(Seq(
        Ex("M", Fn(V("Branch"), Call("Set", V("Nat")))),
        Grp(Seq(All("x", V("Branch")), Call("natBranch", V("x")), Sp, Subseteq, Sp, Call("M", V("x")))),
        Sp, Land, Sp, Grp(Seq(All("x", V("Branch")), All("y", V("Branch")), V("x"), Sp, Neq, Sp, V("y"), Sp, Rightarrow, Sp,
            Call("Finite", Call("inter", Call("M", V("x")), Call("M", V("y")))))),
        Sp, Land, Sp, Call("MADFamily", Call("range", V("M"))), Sp, Land, Sp,
        All("x", V("Branch")), Call("ConvergesOn", V("natValue"), Call("M", V("x")), Call("limitValue", V("x")))));

    private static Formula FiniteUnionStatement => Disp(Seq(
        All("alpha", V("Type")), All("u", Fn(V("alpha"), V("unitInterval"))),
        All("F", Call("Set", Call("Set", V("alpha")))), All("r", V("unitInterval")),
        Call("Finite", V("F")), Sp, Land, Sp,
        Grp(Seq(All("A", Call("Set", V("alpha"))), V("A"), Sp, InMacro, Sp, V("F"),
            Sp, Rightarrow, Sp, Call("ConvergesOn", V("u"), V("A"), V("r")))),
        Sp, Rightarrow, Sp, Call("ConvergesOn", V("u"), Call("sUnion", V("F")), V("r"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Branch-labeled convergent maximal family on Nat.", H("Branch-labeled convergent maximal family on Nat"), Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Describe.Lean(
                DescribeId.Create("finite-sunion-converges"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.finite_sUnion_converges"),
                H("Finite unions converge to a common value"), StatementSource.FromAuthor(FiniteUnionStatement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any carrier alpha, actual value map u, finite family F and common value r, convergence on every member implies convergence on their set union. The proof bounds the exceptional preimage of each neighborhood by the finite union of the memberwise finite exceptions. This is the original supplier, with identical statement, assumptions and proof, exposed at its owner for direct consumption by same-limit threshold-partitioner pairing. No duplicate proof or forwarding wrapper is added. Its exact Reg source telescope is checked, while faithful finite-family variation/raw source reconstruction remains unfinished under https://github.com/the-omega-institute/trureturing/issues/16293."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-branch-labeled-mad"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.exists_branch_labeled_mad"),
                H("Same-limit attachment and natural-number presentation"), StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Additional members of the maximal family are injected into distinct branches at their actual limits. Their power-set cardinal bound is paired with the exact continuum cardinal of each limit fiber. A branch and its assigned member are united; finite disjoint blocks preserve almost-disjointness and convergence. Every old member lies in a new member, so unrestricted maximality is preserved. The nonempty four-letter word carrier is countably infinite and is transported through an actual equivalence with Nat. The resulting M has each original branch inside its corresponding member, finite intersections for distinct labels, unrestricted maximality, and convergence to the same binary limit. This supplies the initial labeled maximal family for the adaptive compact counterexample. It does not assert that a threshold-separating partitioner has been eliminated, or assert the compact topological counterexample or the base classification."))), DescribeRole.Theorem))));
}
