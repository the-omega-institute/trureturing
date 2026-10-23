using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteMenuUnrankingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuUnranking.";
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Nil => Call("nil");
    private static Formula Alpha => Call("of", V("true"));
    private static Formula Number(Formula s) => Call("N", s);
    private static Formula Tree(Formula s, Formula i) => Call("unrank", s, i);
    private static Formula Height(Formula t) => Call("height", t);
    private static Formula Depth(Formula s) => Call("sup", Call("toFinset", s), Call("length"));
    private static Formula Statement()
    {
        var s = V("S");
        var i = V("i");
        var t = Tree(s, i);
        return All("S", V("Menu"), All("i", V("Nat"), And(
            Imp(LeOf(Number(s), i), EqOf(t, Alpha)),
            Imp(EqOf(s, Nil), And(EqOf(t, Alpha), EqOf(Height(t), D(0)))),
            Imp(Less(i, Number(s)), EqOf(Call("code", s, t), i)),
            Imp(NeOf(s, Nil), LeOf(Height(t), Add(D(1), Depth(s)))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native representatives of every ordered-menu rank", H("Native representatives of every ordered-menu rank"), Blocks(
            Paragraph(Text("Source is the existing FreeMagma Bool: of(true) is alpha, of(false) is beta, and mul pairs two actual full binary trees. Addresses use false for L and true for R. A menu is an arbitrary finite ordered list of addresses. Empty lists, epsilon, repeated targets, mixed sides, nested targets and menus lacking prefixes are all included.")),
            Paragraph(Text("For a menu S, let d be the maximum address length, with maximum zero for the empty list. In Lean this is S.toFinset.sup List.length. Passing to a finite set is used only for this maximum; the original ordered child menus, count N, overlap bit eta and numerical code are unchanged. The unrank procedure uses d+1 recursive levels. Each call returns alpha for an empty menu or an invalid natural index.")),
            Paragraph(Text("For a nonempty menu put J=N(SL)N(SR). If i<J, the inverse of finProdFinEquiv supplies the left digit i/N(SR) and right digit i modulo N(SR), each within its original child radix. Recursively build the two child representatives and pair them in one actual tree. The existing equivalence numbers this pair as iL*N(SR)+iR, after commuting addition and multiplication. Index J returns alpha. The sole remaining valid index is J+1 and returns beta; the grammar forces eta to be one in that case. When eta is zero there is no extra beta tag: its original code already belongs to the branch interval.")),
            Paragraph(Text("Correctness is proved by induction on the finite recursion depth. Every child address has one fewer letter, so the induction hypothesis applies simultaneously to both digits. The branch equation and the product equivalence recover i. The two leaf cases use the exact original grammar. A separate induction bounds height by the available recursion depth: leaves have height zero and pairing adds one to the maximum of the child heights. Thus the bound concerns actual tree height, rather than FreeMagma.length.")),
            Describe.Lean(DescribeId.Create("original-menu-unranking"), DeclarationHandle.Create(Prefix + "original_menu_unranking"), H("Total original-rank representatives and height"), StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Every valid original label is attained by the returned tree, without an attained-vector input, a source-height hypothesis or prefix closure. The empty menu always returns height-zero alpha. The nonempty height bound holds even for invalid indices, since their fixed default is alpha.")),
                Paragraph(Text("This is the representative and height part of the finite-menu normal form. It supplies common native realizations of branch digit pairs. It does not establish the converse trajectory classification, a minimum retained alphabet, or physical, runtime and memory optimality."))), DescribeRole.Theorem)
        )));
}
