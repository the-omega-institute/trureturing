using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.NativeContinuation;

internal sealed class NullReplyFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula NatPair => Seq(Natural, Sp, Times, Sp, Natural);
    private static Formula IntegerPair => Seq(Integer, Sp, Times, Sp, Integer);
    private static Formula Words => Call("List", V("Window"));

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-null-fiber-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete natural source histories of the existing high-to-low reader determine the exact appended-null zero fiber.",
        H("Natural Fibonacci Window Histories and the Null Reply Fiber"),
        Blocks(
            Paragraph(Text("Window is the existing five-letter alphabet. Its null, low, high, ends and middle letters have printed low-to-high bits 000, 100, 001, 101 and 010. The existing reader processes windows in the order of the list, rejects when the prior seam and the current high bit are both true, and otherwise replaces the seam by the current low bit. Its clock is three Fibonacci steps S(a,b)=(a+2b,2a+3b), and its quantity is q(a,b)=2a+3b. At modulus zero its coefficient carrier is the integers, with no reduction.")),
            Definition("highBits", "The complete high-to-low bit history",
                "highBits(w) concatenates the reversal of each letter's existing bit list, without reversing the window list. Every window contributes three bits. Thus legal(s,highBits(w)) imposes the incoming high boundary s and every actual seam, while leaving the last seam free. The empty word, leading null windows and all-null words retain their original positions."),
            Definition("bitComposition", "Natural window contributions",
                "bitComposition(b) is the pair (value(1,0,bits(b)),value(0,1,bits(b))) of the existing Fibonacci bit evaluations over the natural numbers. In the order null, low, high, ends, middle these pairs are (0,0), (1,0), (1,1), (2,1), (0,1). They are the natural contributions of the same letters, rather than contributions of another alphabet."),
            Definition("NativeHistory", "Guarded natural source histories",
                "NativeHistory(s,c,w,t,d) is a relation, not an additional reader. An empty word has final seam s and composition c. For a word b followed by v, require that s and last(b) are not both true, then use NativeHistory(first(b),S(c)+bitComposition(b),v,t,d). The initial and final compositions are natural pairs. This retains each source letter and the actual seam at each prefix, with no leading-letter restriction or terminal test."),
            Describe.Lean(DescribeId.Create("native-null-fiber-execution"),
                DeclarationHandle.Create(Prefix + "native_execution"), H("Exact realization by the existing reader"),
                StatementSource.FromAuthor(ExecutionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("R(s,c,w) abbreviates the existing rawMachine(0).toDFA.evalFrom(some(s,residue(0,c)),w). The map residue(0,d) is the coordinatewise natural-to-integer cast. The formula includes both the error equivalence and the equivalence for every candidate successful seam and integer composition.")),
                    Paragraph(Text("Word induction identifies the actual guard with bit legality. The natural bit contributions cast to the existing reader's five displacements, and three natural Fibonacci steps cast to its clock. A rejected prefix remains error for every remaining letter. A successful prefix therefore has natural coordinates following the displayed source recurrence; conversely each such source history realizes that same successful state. The assertion holds for every natural initial composition and either incoming seam."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-null-fiber-zero"),
                DeclarationHandle.Create(Prefix + "null_reply_zero_iff"), H("The exact zero fiber of actual null continuation"),
                StatementSource.FromAuthor(ZeroFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("task(0,w) is the existing immediate output from seam false and composition (0,0). The appended letter is the existing zero window. Its guard is always legal on a live state, it sets the seam to false, and it performs the full clock before returning qS(c)=8a+13b on a natural composition c=(a,b). It leaves error absorbing.")),
                    Paragraph(Text("The exact realization supplies natural coordinates for every successful input. The updated natural composition vanishes precisely when both the prior composition and the current window contribution vanish. Induction on the source history therefore forces every preceding letter to be null when the final composition is zero. Since 8a+13b is zero on the natural cone only at (0,0), the actual appended-null reply is zero precisely on all-null words. The equivalence ranges over every finite input word, including illegal words and the empty word; illegal words return none. On the complete legal words of any fixed length it identifies the zero-reply event with the single all-null source. It does not state a probability law or a spectral relation."))), DescribeRole.Theorem))));

    private static Formula ExecutionFormula()
    {
        var s = V("s"); var c = V("c"); var w = V("w");
        var t = V("t"); var x = V("x"); var d = V("d");
        var r = Call("R", s, c, w);
        var error = IffOf(EqOf(r, V("none")),
            Seq(Neg, Sp, Call("legal", s, Call("highBits", w))));
        var history = Call("NativeHistory", s, c, w, t, d);
        var cast = EqOf(x, Call("residue", D(0), d));
        var live = All("t", V("Bool"), All("x", IntegerPair,
            IffOf(EqOf(r, Call("some", Pair(t, x))), Some("d", NatPair, And(history, cast)))));
        return Disp(All("s", V("Bool"), All("c", NatPair, All("w", Words, And(error, live)))));
    }

    private static Formula ZeroFormula()
    {
        var w = V("w"); var b = V("b");
        var nullLetter = V("zero");
        var singleton = Seq(OpenBracket, nullLetter, CloseBracket);
        var reply = Call("task", D(0), Call("append", w, singleton));
        var zero = EqOf(reply, Call("some", D(0)));
        var member = Seq(b, Sp, InMacro, Sp, w);
        var allNull = All("b", V("Window"), Seq(Par(member), Sp, Implies, Sp,
            Par(EqOf(b, nullLetter))));
        return Disp(All("w", Words, IffOf(zero, allNull)));
    }
}
