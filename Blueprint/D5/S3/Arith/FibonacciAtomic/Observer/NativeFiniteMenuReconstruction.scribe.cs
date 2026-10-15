using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteMenuReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction.";

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp, Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp, Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Rank(Formula s, Formula u) => Call("code", s, u);
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula At(Formula a, Formula u, Formula k) => Call("readout", a, Call("iterate", V("substitution"), k, u));


    private static Formula Statement()
    {
        var h = V("h"); var s = V("S"); var u = V("u"); var f = V("f");
        var q = V("q"); var t = V("t"); var k = V("k");
        var depth = All("q", V("Address"), Imp(Mem(q,s), Less(Len(q),h)));
        var agree = All("q", V("Address"), Imp(Mem(q,s), EqOf(Call("f",q), Call("readout",q,u))));
        var trajectory = All("q", V("Address"), Imp(Mem(q,s), All("k", V("Nat"), EqOf(At(q,t,k), At(q,u,k)))));
        var result = Some("t", V("Source"), And(EqOf(Call("reconstruct",h,s,f), Call("some",t)),
            Le(Call("height",t),h), EqOf(Rank(s,t),Rank(s,u)), trajectory));
        return All("h",V("Nat"),All("S",V("Menu"),All("u",V("Source"),All("f",Arr(V("Address"),V("Reply")),
            Imp(And(Call("PrefixClosed",s),depth,agree),result)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix-menu reconstruction", H("Prefix-menu reconstruction"), Blocks(
            Paragraph(Text("PrefixClosed requires every prefix, including epsilon and the member itself, to be selected. The empty menu is prefix-closed. Initial and future vectors use exactly the original list order. A nonempty closed menu contains the root, and both child menus remain prefix-closed.")),
            Paragraph(Text("Reconstruct uses the supplied root reply. Alpha or beta is accepted only when every selected strict descendant is absent. An absent root is rejected. A branch recursively reconstructs the two child menus and pairs their actual representatives. An empty menu returns alpha without inspecting any reply. At zero fuel a nonempty menu rejects.")),
            Paragraph(Text("The depth hypothesis is strict length(q)<h. Every branch descent reduces both fuel and target length. The theorem supplies one actual representative for the whole vector; its code and every future reply agree simultaneously with the original tree. It does not assign independent signatures to coordinates.")),
            Describe.Lean(DescribeId.Create("prefix-menu-reconstruction"), DeclarationHandle.Create(Prefix + "prefix_menu_reconstruction"), H("Every attained vector reconstructs correctly"), StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Induction on h accepts actual leaves with all selected strict descendants absent. For an actual branch the child induction hypotheses give two representatives of height at most h-1. Pairing preserves the original mixed-radix code. Native substitution preserves a reached branch, so each future selected reply reduces to the corresponding child equality at the same count."))), DescribeRole.Theorem))));
}
