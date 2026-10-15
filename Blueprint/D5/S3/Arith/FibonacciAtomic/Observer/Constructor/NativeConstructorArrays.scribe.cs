using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class NativeConstructorArraysDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeConstructorArrays", H("Native constructor array reconstruction"), Blocks(
            Paragraph(Text("The source is the free ordered Boolean tree, with true labelling alpha. Allowed consists exactly of branch/alpha, branch/beta, branch/branch, alpha/absent, beta/absent and absent/absent. Edges checks these pairs at every represented parent and child. Root nonabsence is a separate hypothesis. Neither predicate refers to an existing realization.")),
            Paragraph(Text("Write alpha = Source.of true, beta = Source.of false and C0 = Source.mul alpha alpha. Canonical 0 t means t = alpha. Canonical (k+1) accepts either labelled leaf, and Canonical (k+1) (Source.mul l r) means Canonical k l and Canonical k r. Hence S d = {t : Source | Canonical d t} has S1 = {alpha,beta,C0} and S(k+1) = {alpha,beta} disjoint-union {Source.mul l r | l,r in S k} for positive k. The depth-zero auxiliary carrier fixes the two children of each cutoff branch to alpha; it is not an extra represented coordinate.")),
            Paragraph(Text("Address is a Boolean word, with false = L and true = R. W d = {w : Address | w.length < d}, including the empty root word when d is positive. For z : W d -> Reply, extend z w is z w inside this menu and absent outside it. Edges d z a means that Allowed (z (a ++ w)) (z (a ++ w ++ [b])) holds for every Boolean b and every w with w.length + 1 < d. H d = {z : W d -> Reply | extend z [] is not absent and Edges d (extend z) []}. Thus H is defined by the root condition and six local pairs, independently of any matching tree. Reply consists exactly of alpha, beta, branch and absent.")),
            Describe.Lean(DescribeId.Create("native-constructor-legal-realization"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.legal_realization"),
                H("Literal realization of independently legal arrays"),
                StatementSource.FromAuthor(Disp(All("d", V("Nat"), All("z", Arr(V("Address"), V("Reply")), All("a", V("Address"),
                    Imp(Call("Edges", V("d"), V("z"), V("a")),
                    Imp(Imp(Lt(D(0), V("d")), Ne(Call("z", V("a")), V("absent"))),
                    And(Call("Canonical", V("d"), Call("realize", V("d"), V("z"), V("a"))),
                    All("w", V("Address"), Imp(Lt(Call("length", V("w")), V("d")),
                        EqOf(Call("readout", V("w"), Call("realize", V("d"), V("z"), V("a"))),
                            Call("z", Call("append", V("a"), V("w")))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Reconstruction uses NativeWholeRowService.decodePattern and NativeDepthPatterns.fill with a constant alpha frontier. The proof derives absence below an early leaf directly from the six pairs and recursively realizes both subarrays below a branch. It proves the literal replies for every represented word, with no actual-matching-tree hypothesis and no realization choice.")),
                    Paragraph(Text("This result supplies the array-to-tree direction. The complete representation below consumes this independent reconstruction in both inverse laws. The six-pair induction supplies the independent native reconstruction; finite product and coordinate arithmetic reuse that correspondence."))), DescribeRole.Theorem)
            ,Describe.Lean(DescribeId.Create("native-faithful-constructor-representation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.faithful_constructor_representation"),
                H("Faithful constructor representation on the whole native carrier"),
                WholeStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every positive d and n, S d is the subtype of the original FreeMagma Bool satisfying Canonical d, with true = alpha, false = beta and C0 the ordered pair of alpha leaves. The statement explicitly proves S1 = {alpha,beta,C0}; the successor pair membership is exactly membership of each child in the preceding carrier. Both native labelled leaves remain in every positive carrier. This is the source recursion, not an arbitrary height bound.")),
                    Paragraph(Text("W d consists of exactly the actual Boolean words of length less than d. H d is the subtype of arrays on W d with nonabsent root and precisely the independent six parent/append-bit-child pairs. Total extension outside W d is irrelevant padding by absent. Native readout satisfies the constraints; independent reconstruction supplies a canonical native tree and every represented literal reply. Canonical uniqueness proves the left inverse, and the literal reconstruction law proves the right inverse.")),
                    Paragraph(Text("The displayed binders hd : 0 < d and hn : 0 < n are exactly the original hypotheses, with no upper bound on d or n. scalarReadout d hd maps t : S d to the legal array w |-> readout w.val t.val. scalarReconstruct d z is realize d (extend z.val) [] with its proved Canonical property. scalarEquiv uses exactly these forward and inverse functions and proves both inverse laws. productEquiv d n hd applies scalarEquiv in every Fin n component, and its inverse applies scalarReconstruct componentwise. The displayed literal equality therefore concerns the same tuple x and the same pair (i,w), retaining all correlations, early leaves and absent coordinates.")),
                    Paragraph(Text("The coordinate count is a cardinality of Fin n times W d, not the length of a list with possible repetitions: the prefix list is proved duplicate-free and its exact count is reused. There are n(2^d-1) distinct coordinates and exactly four possible Reply symbols. Repeated uses of (i,w) are one function application and one actual reply. At the cutoff a branch reconstructs C0, whose two alpha children lie just outside W d. An early alpha or beta forces every represented proper descendant absent. The deterministic decodePattern and constant-alpha fill introduce no auxiliary realization choice.")),
                    Paragraph(Text("This is a native representation theorem. It adds no preparation or reader port, recovers no arbitrary unobserved deeper labels and makes no resource or literature-originality claim. The canonical boundary, actual source and literal addresses are those of the source theorem."))), DescribeRole.Theorem)
        )));
    private static StatementSource WholeStatement()
    {
        var alpha = Call("of", V("true"));
        var beta = Call("of", V("false"));
        var c0 = Call("mul", alpha, alpha);
        var baseCarrier = All("t", V("Source"), IffOf(Call("Canonical", D(1), V("t")),
            Or(EqOf(V("t"), alpha), Or(EqOf(V("t"), beta), EqOf(V("t"), c0)))));
        var successor = All("k", V("Nat"), All("l,r", V("Source"),
            IffOf(Call("Canonical", Seq(V("k"), Sp, Plus, Sp, D(1)), Call("mul", V("l"), V("r"))),
                And(Call("Canonical", V("k"), V("l")), Call("Canonical", V("k"), V("r"))))));
        var productReply = new Formula.Apply(Call("val",
            Call("productEquiv", V("d"), V("n"), V("hd"), V("x"), V("i"))), [V("w")]);
        var literal = All("x", Arr(Call("Fin", V("n")), Call("S", V("d"))),
            All("i", Call("Fin", V("n")), All("w", Call("W", V("d")),
                EqOf(productReply,
                    Call("readout", Call("val", V("w")), Call("val", Call("x", V("i"))))))));
        var coordinates = EqOf(Call("card", Call("Prod", Call("Fin", V("n")), Call("W", V("d")))),
            Seq(V("n"), Sp, Times, Sp, Open, Seq(D(2), Caret, Grp(V("d"))), Sp, Minus, Sp, D(1), Close));
        var scalar = Call("Bijective", Call("scalarReadout", V("d"), V("hd")));
        var product = Call("Bijective", Call("productEquiv", V("d"), V("n"), V("hd")));
        var conclusion = And(baseCarrier, And(successor, And(scalar, And(product,
            And(literal, And(coordinates, EqOf(Call("card", V("Reply")), D(4))))))));
        return StatementSource.FromAuthor(Disp(All("d,n", V("Nat"),
            All("hd", Lt(D(0), V("d")), All("hn", Lt(D(0), V("n")), conclusion)))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..xs]);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Or(Formula a, Formula b) => Seq(Open, a, Close, Sp, Lor, Sp, Open, b, Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Close, Sp, Iff, Sp, Open, b, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Seq(n.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()), Colon, Sp, t, Comma, Sp, Open, b, Close);
}
