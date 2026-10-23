using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeDepthPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeDepthPatterns", H("NativeDepthPatterns"), Blocks(
            Entry("original_present_transport", "Originally present subtree transport", "For every epoch, an originally present subtree is transported to its iterated native substitution at the same original address. There is no unconditional Option.map law at originally absent addresses; substitution can create physical descendants below original leaves.", DescribeRole.Theorem),
            Entry("original_prefix_locality", "All-epoch original-prefix locality", "SLH.74.7 holds for every natural epoch, including zero, and every physical address, including addresses originally absent and later born. The proof follows the original path, then evolves the first original leaf. Pair preservation directly applies Function.Semiconj\u2082.iterate.", DescribeRole.Theorem),
            Entry("Pattern", "Finite reached-frontier patterns", "At zero depth the whole source is one hole. At positive depth an original leaf terminates the branch, while an original pair exposes two shallower patterns. The recursive Fintype instance enumerates precisely these finite possibilities.", DescribeRole.Definition),
            Entry("Frontier", "Actual frontier variable positions", "Unit supplies the reached depth-zero position. An early leaf supplies the empty type. An ordered pair supplies the disjoint sum of its child frontiers. Thus names are positions, not values and not a hidden inequality requirement.", DescribeRole.Definition),
            Entry("fill", "Unrestricted native fillings", "Every variable receives an arbitrary finite nonempty Boolean free tree. Different positions may receive the same tree. No finite tree universe or source-size bound is imposed.", DescribeRole.Definition),
            Entry("depthEquiv", "Unique decomposition and reconstruction", "The equivalence constructs the unique pattern and its actual frontier subtrees, with inverse fill. This retains every filling and every original tree, including zero variables.", DescribeRole.Definition),
            Entry("frontier_geometry", "All and only reached depth positions", "Each frontier name has address length d and recovers its assigned actual subtree. Conversely, at every length-d address, presence after filling is equivalent to that address naming a frontier variable. Early original leaves remain absence guards.", DescribeRole.Theorem),
            Entry("Consistent", "Complete mixed-epoch history", "Each listed event uses the actual iterated substitution and four-valued reply. Repeated events remain conjuncts, and absent replies have the native presence guard. Inconsistent lists remain valid inputs.", DescribeRole.Definition)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativedepthpatterns-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n switch
    {
        "original_present_transport" => StatementSource.FromAuthor(Disp(All("n", V("Nat"), All("a", V("Address"), All("u,t", V("Source"), Imp(EqOf(Call("subtree", V("a"), V("u")), Call("some", V("t"))), EqOf(Call("subtree", V("a"), Call("iterate", V("substitution"), V("n"), V("u"))), Call("some", Call("iterate", V("substitution"), V("n"), V("t")))))))))),
        "original_prefix_locality" => StatementSource.FromAuthor(Disp(All("n", V("Nat"), All("s", V("Address"), All("u,v", V("Source"), Imp(All("a", V("Address"), Imp(LessEq(Call("length", V("a")), Call("length", V("s"))), EqOf(Call("readout", V("a"), V("u")), Call("readout", V("a"), V("v"))))), EqOf(Call("readout", V("s"), Call("iterate", V("substitution"), V("n"), V("u"))), Call("readout", V("s"), Call("iterate", V("substitution"), V("n"), V("v")))))))))),
        "frontier_geometry" => StatementSource.FromAuthor(Disp(All("d", V("Nat"), All("p", Call("Pattern", V("d")), And(All("x", Call("Frontier", V("p")), EqOf(Call("length", Call("frontierAddress", V("p"), V("x"))), V("d"))), All("f", Arr(Call("Frontier", V("p")), V("Source")), All("x", Call("Frontier", V("p")), EqOf(Call("subtree", Call("frontierAddress", V("p"), V("x")), Call("fill", V("p"), V("f"))), Call("some", Call("f", V("x")))))), All("f", Arr(Call("Frontier", V("p")), V("Source")), All("a", V("Address"), Imp(EqOf(Call("length", V("a")), V("d")), IffOf(Call("isSome", Call("subtree", V("a"), Call("fill", V("p"), V("f")))), Some("x", Call("Frontier", V("p")), EqOf(Call("frontierAddress", V("p"), V("x")), V("a")))))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula LessEq(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
