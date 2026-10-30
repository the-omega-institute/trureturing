using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class PhysicalTapeDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete direction functions determine finite ordered terminal frontiers.",
        H("Physical Direction Tapes and Paid Terminal Tests"), Blocks(
            Paragraph(Text("Source is FreeMagma Bool, the existing finite nonempty ordered full binary tree. "
                + "Its leaf labels are alpha (true) and beta (false). An Address is a finite Boolean list: "
                + "false is physical a, true is physical b, and concatenation is written append. "
                + "readout has the existing four values alpha, beta, branch and absent. Only absence "
                + "versus presence is used by the walks. Height is the height of the existing ordered "
                + "shape decompose(T).1, so a leaf has height zero.")),
            Def("depth", "Direction depth", "A leaf returns zero for every tape. At a branch a leading "
                + "false chooses the left child and a leading true chooses the right child; the result "
                + "is one plus the child's depth on the tail. The total definition returns zero at an "
                + "exhausted branch. Every walk asserted below has enough remaining directions to "
                + "reach a leaf, and therefore never uses that extra case."),
            Def("probes", "Full root query operands", "At the current physical address p the first "
                + "operand is append(p,[false]), including at a terminal node with an empty tape. "
                + "After choosing b the next current address is append(p,[b]). The list retains "
                + "every query operand, in chronological order, including the final absent-child test."),
            Def("PaidWalk", "Paid presence walk", "PaidWalk(U,p,u,tr,d) is the finite serial derivation "
                + "in the same full root U. A stop requires readout(append(p,[false]),U)=absent and "
                + "records that operand. A step requires its presence, consumes one direction b, "
                + "continues at append(p,[b]), and increments the edge count. Exhaustion alone is "
                + "not a stop rule. This is a mathematical description of the original stationary "
                + "presence service; root binding, grants, backing and completed serial reads remain "
                + "premises for using that service."),
            Describe.Lean(DescribeId.Create("physical-tape-depth-geometry"),
                DeclarationHandle.Create(Prefix + "tape_geometry"), H("Complete tape geometry"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All tree, literal, tape and horizon quantifiers are unrestricted. "
                        + "The location hypothesis compares every suffix in the same full root, "
                        + "rather than supplying a second relative root. Induction on the finite "
                        + "tree proves the paid walk, the exact number depth+1 of reads, the all-tape "
                        + "height bound, and independence from every appended padding word. Choosing "
                        + "a child of maximum height recursively attains the bound at every sufficient horizon.")),
                    Paragraph(Text("An existing subtree at p gives both its remaining height bound "
                        + "and the exact prefix offset for every suffix tape. Equal complete depth "
                        + "functions force matching terminal reports after erasing the leaf labels. "
                        + "The existing source_foundation complete-frontier rigidity theorem then "
                        + "identifies the ordered unlabelled shapes. No leaf-label recovery, future "
                        + "observation equivalence, source acquisition or resource bound follows."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("physical-tape-depth-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] x) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. x]);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) =>
        Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] x) => Seq(x.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, RowBreak, Par(f))).ToArray());
    private static Formula Len(Formula u) => Call("length", u);
    private static Formula Ht(Formula t) => Call("height", t);
    private static Formula Dp(Formula t, Formula u) => Call("depth", t, u);
    private static Formula App(Formula a, Formula b) => Call("append", a, b);
    private static Formula Shape(Formula t) => Seq(Call("decompose", t), Dot, D(1));
    private static Formula Result()
    {
        var t=V("T"); var u=V("u"); var v=V("v"); var root=V("U");
        var p=V("p"); var w=V("w"); var l=V("L");
        var source=V("Source"); var address=V("Address"); var nat=V("Nat");
        var enough=LeOf(Ht(t),Len(u));
        return All("T", source, And(
            All("U",source,All("p",address,All("u",address,
                Imp(All("w",address,EqOf(Call("readout",App(p,w),root),Call("readout",w,t))),
                    Imp(enough,Call("PaidWalk",root,p,u,Call("probes",t,p,u),Dp(t,u))))))),
            All("p",address,All("u",address,EqOf(Len(Call("probes",t,p,u)),Add(Dp(t,u),D(1))))),
            All("u",address,LeOf(Dp(t,u),Ht(t))),
            All("u",address,All("v",address,Imp(enough,EqOf(Dp(t,App(u,v)),Dp(t,u))))),
            All("L",nat,Imp(LeOf(Ht(t),l),Some("u",address,And(EqOf(Len(u),l),EqOf(Dp(t,u),Ht(t)))))),
            All("U",source,All("p",address,
                Imp(EqOf(Call("subtree",p,root),Call("some",t)),And(
                    LeOf(Add(Len(p),Ht(t)),Ht(root)),
                    All("u",address,EqOf(Dp(root,App(p,u)),Add(Len(p),Dp(t,u)))))))),
            All("U",source,All("L",nat,Imp(LeOf(Ht(t),l),Imp(LeOf(Ht(root),l),
                Imp(All("u",address,Imp(EqOf(Len(u),l),EqOf(Dp(t,u),Dp(root,u)))),
                    EqOf(Shape(t),Shape(root)))))))));
    }
}
