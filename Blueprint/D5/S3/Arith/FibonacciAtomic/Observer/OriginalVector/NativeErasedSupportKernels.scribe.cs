using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector;

internal sealed class NativeErasedSupportKernelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeErasedSupportKernels", H("Native erased and support prefix kernels"), Blocks(
            Describe.Lean(
                DescribeId.Create("native-reply-erasure"), Handle("erase"), H("Leaf erasure"),
                StatementSource.FromAuthor(Disp(And(
                    Eq(Call("erase", V("alpha")), V("leaf")),
                    Eq(Call("erase", V("beta")), V("leaf")),
                    Eq(Call("erase", V("branch")), V("branch")),
                    Eq(Call("erase", V("absent")), V("absent"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ErasedReply has the three constructors leaf, branch, and absent. Erasure identifies exactly the alpha and beta leaf replies. In particular, an absent address remains distinct from a leaf and from a branch."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-erased-prefix"), Handle("ErasedAgree"), H("Erased prefix agreement"),
                StatementSource.FromAuthor(Disp(AllSources("r", IffOf(E(V("r"), V("u"), V("v")),
                    All("a", V("Address"), Imp(Le(Len(V("a")), V("r")),
                        Eq(Call("erase", Read(V("a"), V("u"))), Call("erase", Read(V("a"), V("v")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ErasedAgree compares all erased replies at ordered addresses of length at most the radius. Addresses below an original leaf are included and return absent."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-support-prefix"), Handle("SupportAgree"), H("Presence prefix agreement"),
                StatementSource.FromAuthor(Disp(AllSources("r", IffOf(S(V("r"), V("u"), V("v")),
                    All("a", V("Address"), Imp(Le(Len(V("a")), V("r")),
                        IffOf(Present(V("a"), V("u")), Present(V("a"), V("v"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SupportAgree retains only whether each address is present. On full binary trees, the presence of an address and of one specified child distinguishes absent, leaf, and branch. Thus erased agreement through radius r is equivalent to presence agreement through radius r+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-two-step-prefix-kernel"), Handle("two_step_prefix_kernel"), H("Exact two-step kernels"),
                StatementSource.FromAuthor(Disp(TwoStep())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Source is FreeMagma Bool, the finite nonempty ordered binary trees. The source leaf of(true) is alpha and of(false) is beta. The actual substitution rho sends alpha to beta and beta to mul(beta,alpha), and distributes over ordered branches. Addresses are Boolean lists, with false left and true right. OriginalAgree compares the complete four-valued readout through an inclusive natural radius.")),
                    Paragraph(Text("After two substitutions every source has a branch root. The erased child replies of an original alpha, beta, and branch are respectively (leaf,leaf), (branch,leaf), and (branch,branch). They recover the original root type. Induction on the radius then transports labeled agreement one layer deeper and reflects erased agreement back to the original prefix. Below a recovered leaf the original replies are absent, even if substitution has created current descendants.")),
                    Paragraph(Text("For every radius h and every pair of sources, the original labeled prefix has the same equality classes as the labeled or erased two-step prefix through h+1, and as the presence prefix through h+2. The root, left-right order, and source pair are the same throughout."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-even-epoch-support-kernel"), Handle("even_epoch_support_kernel"), H("All positive even epochs"),
                StatementSource.FromAuthor(Disp(EvenEpoch())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At every certified epoch 2k with k at least one, the erased prefix through h+k and the presence prefix through h+k+1 each determine exactly the original labeled prefix through h. Iterating the labeled component of the two-step equality transports the radius through the preceding k-1 pairs of substitutions; the final two-step equality gives the erased and presence conclusions.")),
                    Paragraph(Text("All natural radii and all finite sources are included, without a source-size promise. The statement compares observations at a fixed actual epoch on the original root. Sharpness of the presence radius follows from the existing native alpha-spine observation theorem: choose an original address of length h and put alpha and beta at that reached hole. Their original replies there differ while their presence tables agree through h+k."))
                ), DescribeRole.Theorem)
        )));

    private static Formula TwoStep()
    {
        var h = V("h"); var u = V("u"); var v = V("v");
        var cu = Current(D(2), u); var cv = Current(D(2), v);
        return AllSources("h", And(
            IffOf(A(h, u, v), A(Add(h, D(1)), cu, cv)),
            IffOf(A(h, u, v), E(Add(h, D(1)), cu, cv)),
            IffOf(A(h, u, v), S(Add(h, D(2)), cu, cv))));
    }

    private static Formula EvenEpoch()
    {
        var h = V("h"); var k = V("k"); var u = V("u"); var v = V("v");
        var cu = Current(Mul(D(2), k), u); var cv = Current(Mul(D(2), k), v);
        var clauses = And(
            IffOf(E(Add(h, k), cu, cv), A(h, u, v)),
            IffOf(S(Add(Add(h, k), D(1)), cu, cv), A(h, u, v)));
        return All("h", V("Nat"), All("k", V("Nat"), Imp(Le(D(1), k),
            All("u", V("Source"), All("v", V("Source"), clauses)))));
    }

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels." + name);
    private static Formula A(Formula r, Formula u, Formula v) => Call("OriginalAgree", r, u, v);
    private static Formula E(Formula r, Formula u, Formula v) => Call("ErasedAgree", r, u, v);
    private static Formula S(Formula r, Formula u, Formula v) => Call("SupportAgree", r, u, v);
    private static Formula Read(Formula a, Formula u) => Call("readout", a, u);
    private static Formula Present(Formula a, Formula u) => Seq(Read(a, u), Sp, Neq, Sp, V("absent"));
    private static Formula Current(Formula n, Formula u) => Call("iterate", V("substitution"), n, u);
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula AllSources(string radius, Formula body) => All(radius, V("Nat"),
        All("u", V("Source"), All("v", V("Source"), body)));
    private static Formula All(string n, Formula t, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(body));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
}
