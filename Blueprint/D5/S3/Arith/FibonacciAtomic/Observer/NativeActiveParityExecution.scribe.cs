using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativeActiveParityExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeActiveParityExecution", H("Expanded active parity execution"), Blocks(
            Paragraph(Text("Every public full ordered skeleton S supplies a chart by numbering its leaves from left to right and constructing their literal addresses recursively. The labels already on S are ignored, so the chart depends only on its shape. Writing h for the leaf count of S, this chart is a full ordered literal skeleton with h leaves and one fixed address for each index from zero to h minus one. At that address its literal subtree is the corresponding indexed variable, and the skeleton has exactly h leaves. Each original label x(i) is independent: false means alpha and true means beta. Filling the skeleton with the atomic sources of ranks bit(x(i)) defines the original source. The unknown entry lag t applies substitution to this same source. The observation at runtime epoch j is its literal readout after t plus j substitutions; j counts genuine post-entry Updates and is proof data, not a controller register.")),
            Paragraph(Text("The expanded table retains Q(i,a) for zero through h, B(i,a,b) and C(i,b) for zero through h minus one, and V(a,01), V(a,11), V(a,10), for both Boolean accumulators and every latch bit. At nonterminal Q(i,a), the literal is the chart's address i followed by K right edges. At i equal to zero, absence selects V(a,01), branch holds Q(0,a), and either leaf reply selects B(0,a,a XOR chi(reply)). At positive i, all four replies select that B row. The decoder chi is true on absence and beta and false on alpha and branch.")),
            Paragraph(Text("V(a,01) and V(a,11) each execute one genuine Update. V(a,10) performs a root Read and returns to Q(0,a) on every reply. Every B row performs a root Read: unequal accumulator and latch bits select B(i,b,b), while equal bits select C(i,b). Every C row performs a root Read and selects Q(i+1,b). These Reads retain the actual source and discard their raw reply. Q(h,a) halts with the fixed output a. There are no internal instructions. The B and C notation distinguishes the before-advance and after-advance latch positions of the expanded table; it does not establish a binary encoding.")),
            Describe.Lean(
                DescribeId.Create("native-active-parity-execution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.native_active_parity_execution"),
                H("Original parity and exact update endpoint"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The statement ranges over every full original skeleton, whose chart is constructed without a native observation premise, and all independently chosen labels, and all entries with t at most twice K. Its admissible regimes are even h or zero entry lag. In the bounded source promise t at most T, choosing K as the ceiling of T divided by two supplies this bound; when T is zero, t is zero. The original output is the XOR of all h labels, written parity(labels(x),h). A finite Run to a halt has precisely that fixed output, the displayed number of genuine Updates, and the fixed Halt payload equal to that original XOR.")),
                    Paragraph(Text("The pilot alignment theorem is applied to the actual first cone of rank t plus bit(x(0)). Its existing Run retains both Updates and the paid return Read. Induction on that Run splices its terminal leaf reply into the B latch route. If J is its terminal update epoch, every original cone then has rank t plus J plus bit(x(i)), in the interval from twice K minus one through twice K plus two. The exact four-reply clock law proves that chi equals rank parity on this acquired window. Since J is even, each accepted bit is (t modulo two) XOR x(i).")),
                    Paragraph(Text("Induction over the remaining stages uses the concrete data Read and the two or three concrete latch-routing root Reads at each stage. The accumulator is the XOR of the accepted prefix. The common offset cancels for even h, and is zero when t is zero. The constructed actual Run reaches the asserted halt. Native halt uniqueness supplies the converse and the fixed endpoint, including its update epoch.")),
                    Paragraph(Text("The pilot branch hold has no promised support under the rank bound, and no off-promise termination is asserted. Chi is not a parity decoder for arbitrary saturated branches or arbitrarily deep absent addresses. This result establishes the entire expanded symbolic table's actual-source execution. Its realization as one injective immediate binary word with no adjacent ones remains a separate obligation, together with all encoding edges, width and installed-word counts for arbitrary h and the complete primitive, address and bit-change bills. No mutable-width or physical execution-service claim follows from this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cone-read"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.cone_read"),
                H("Literal readout on an original cone"),StatementSource.FromAuthor(Disp(ConeStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any supplied Chart with h independently indexed original leaves, any label assignment, entry lag t, post-entry update epoch j, original index i and arbitrary literal suffix p, the physical readout at address(i) followed by p equals the readout of p on the atom of rank t+j+bit(x(i)). The atom on the right is the actual original cone of that source at epoch j. This identity imposes no alignment-window premise and is used for the static scan as well as the active alignment. The label convention remains atom(bit(x(i))), with alpha equal to of(true) and beta equal to of(false)."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shifted-parity"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.shifted_parity"),
                H("Common Boolean offset in a finite parity"),StatementSource.FromAuthor(Disp(ShiftStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write shift(b,x)(i)=b XOR x(i). The XOR of its first n entries is the original prefix XOR, with one additional b exactly when n is odd. Even n cancels the common offset; a false offset vanishes for every n. This identity is used after deriving the actual scheduled contributions."))),DescribeRole.Theorem))));

    private static Formula ConeStatement() {
        var h=V("h"); var C=V("C"); var x=V("x"); var t=V("t"); var j=V("j"); var i=V("i"); var p=V("p");
        var n=Seq(t,Sp,Plus,Sp,j,Sp,Plus,Sp,Call("bit",Call("x",i)));
        return All("h",V("Nat"),All("C",Call("Chart",h),All("x",Seq(Call("Fin",h),Sp,To,Sp,V("Bool")),
            All("t",V("Nat"),All("j",V("Nat"),All("i",Call("Fin",h),All("p",V("Address"),
                Eq(Call("observations",C,t,x,j,Call("append",Call("address",C,i),p)),Call("readout",p,Call("atom",n))))))))));
    }
    private static Formula ShiftStatement() {
        var x=V("x"); var b=V("b"); var n=V("n");
        return All("x",Seq(V("Nat"),Sp,To,Sp,V("Bool")),All("b",V("Bool"),All("n",V("Nat"),
            Eq(Call("parity",Call("shift",b,x),n),Call("xor",
                Call("and",Call("decide",Eq(Call("mod",n,D(2)),D(1))),b),Call("parity",x,n))))));
    }
    private static Formula Statement()
    {
        var S = V("S"); var C = Call("chartOf", S); var h = Call("length", S);
        var x = V("x"); var t = V("t"); var K = V("K"); var b = V("b"); var N = V("N");
        var twoK = Seq(D(2), K);
        var original = Call("parity", Call("labels", x), h);
        var firstRank = Seq(t, Sp, Plus, Sp, Call("bit", Call("x", D(0))));
        var count = Seq(D(2), Par(Seq(K, Sp, Minus, Sp, Call("div", firstRank, D(2)))));
        var run = Call("Run", Call("program", C, K), Call("observations", C, t, x),
            Call("start", h), D(0), Call("endpoint", h, b), N);
        var result = And(Eq(b, original), And(Eq(N, count),
            Eq(Call("output", Call("endpoint", h, b)), Call("some", original))));
        var endpoint = All("b", V("Bool"), All("N", V("Nat"), IffOf(run, result)));
        var admissible = Or(Eq(Call("mod", h, D(2)), D(0)), Eq(t, D(0)));
        var body = Imp(Le(t, twoK), Imp(admissible, endpoint));
        return All("S", V("Source"),
            All("x", Seq(Call("Fin", h), Sp, To, Sp, V("Bool")),
                All("t", V("Nat"), All("K", V("Nat"), body))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
