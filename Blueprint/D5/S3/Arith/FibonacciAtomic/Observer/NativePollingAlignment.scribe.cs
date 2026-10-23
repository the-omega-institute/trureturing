using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativePollingAlignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativePollingAlignment", H("Native polling alignment"), Blocks(
            Paragraph(Text("A source is a finite nonempty ordered Boolean tree. The true leaf is alpha and the false leaf is beta. Substitution sends alpha to beta and beta to the ordered pair of beta and alpha, and acts on both children of every branch. The right clock is zero on alpha, one on beta, and two plus the right child's clock on a branch. An address bit false means left and true means right; rights K is the literal consisting of K right edges.")),
            Paragraph(Text("The complete program has four nonterminal controls, poll, firstUpdate, secondUpdate and route, and two terminal controls done false and done true. Poll reads rights K. Alpha selects done false, beta selects done true, absence selects firstUpdate, and branch selects poll. The first two retry controls each perform one genuine substitution update. Route then performs a root Read and selects poll for every reply. The root Read is a separate native action and does not change the source. Both done controls halt.")),
            Describe.Lean(
                DescribeId.Create("native-polling-alignment"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment.native_polling_alignment"),
                H("Exact terminal bit and update epoch"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The observation field at epoch j is the literal readout of the j-fold substituted original source u. Run starts at poll and epoch zero, and retains each Read and each Update of the displayed program. Its terminal epoch N counts real updates. For every source whose initial right clock is at most twice K plus one, a run reaches done b precisely for the displayed bit and update count. This includes K equal to zero and either clock parity.")),
                    Paragraph(Text("Write the initial clock as twice its quotient by two plus its remainder. While a retry remains, the clock at the polling Read is below twice K, so the actual reply is absent. Two updates advance that clock by two; the intervening root Read only routes control. Induction on the number of remaining retries reaches clock twice K plus its original remainder. Its reply is alpha or beta, selecting the asserted terminal bit. Determinism of native runs identifies every halt endpoint with this constructed endpoint.")),
                    Paragraph(Text("The clock promise is essential to this conclusion: branch at the pilot is an unsupported hold. The result describes the concrete same-source control program and its update epoch. It supplies no one-bit encoding, physical execution service, or theorem about recovery of all original leaf labels. In particular, the root routing Read is retained rather than contracted into an update."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var K = V("K");
        var u = V("u");
        var b = V("b");
        var N = V("N");
        var clock = Call("rightClock", u);
        var bit = Call("decide", Eq(Call("mod", clock, D(2)), D(1)));
        var count = Seq(D(2), Par(Seq(K, Sp, Minus, Sp,
            Call("div", clock, D(2)))));
        return All("K", V("Nat"), All("u", V("Source"), Imp(
            Le(clock, Seq(D(2), K, Sp, Plus, Sp, D(1))),
            All("b", V("Bool"), All("N", V("Nat"), IffOf(
                Call("Run", Call("program", K), Call("observations", u),
                    V("poll"), D(0), Call("done", b), N),
                And(Eq(b, bit), Eq(N, count))))))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
