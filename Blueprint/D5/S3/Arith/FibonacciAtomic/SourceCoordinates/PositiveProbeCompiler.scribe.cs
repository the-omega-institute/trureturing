using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class PositiveProbeCompilerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A public finite compiler implements every shifted terminal gcd in two consecutive "
            + "Fibonacci directions using only short positive replacement and graft words.",
        H("Effective short positive probes"),
        Blocks(
            Paragraph(Text("The actual source is any natural pair v=(a,b), including (0,0). "
                + "The original calls are R(a,b)=(b,a+b) and G(a,b)=(a+1,b). "
                + "A Boolean word is chronological: true means R and false means G. "
                + "Run(W,v) is TerminalGcdAcquisitionCost.runWord, not an independently "
                + "assumed simulator. Quantity is q(a,b)=2a+3b. A terminal read returns "
                + "gcd(q Run(W,v),H). A word contains no read instruction: its execution "
                + "precedes one separately paid current read.")),
            Definition("direction", "The original least direction", Direction(),
                "K(H)=direction(H) is the least k>=1 with H<=fib(k+4). The terminating "
                + "natural-number search uses the unbounded Fibonacci sequence; it does "
                + "not select a direction from the unknown source. The convention is "
                + "fib(0)=0, fib(1)=1."),
            Definition("graftBound", "The graft allowance", Bound(),
                "Gamma(H)=graftBound(H)=1+floor((K(H)+2)/2), equivalently "
                + "1+ceil((K(H)+1)/2). This counts individual original graft calls."),
            Definition("positiveLift", "An executable shift representative", Lift(),
                "Let d=c mod H. The representative t(H,c) is zero when d=0, H+1 "
                + "when d=1, and d otherwise. For H>1 a nonzero representative lies "
                + "between 2 and H+1. In particular an offset of one never requests "
                + "an unavailable unit-weight action."),
            Definition("weights", "A finite list of available weights", Weights(),
                "Z(H,c)=weights(H,c) is empty when c mod H=0. Otherwise let "
                + "z=Nat.zeckendorf(t(H,c)-2), the existing descending list of occupied "
                + "Fibonacci indices. Remove index 2, then append index 4 if z contains "
                + "2, or index 3 otherwise. The filter removes the auxiliary weight "
                + "fib(2)=1. The appended weight replaces the reserved 2 together with "
                + "that auxiliary 1 by 3 when necessary. Repeated indices 3 or 4 are "
                + "permitted: they mean repeated graft calls, not a larger primitive."),
            Definition("emit", "Chronological emission from descending weights", Emit(),
                "E(k,l)=emit(k,l) treats k as the number of replacements still to "
                + "emit. For an empty list it emits R repeated k times. For i::l it "
                + "emits R repeated k-(i-3) times, then one G, then E(i-3,l). "
                + "All subtractions in this total definition are truncated natural "
                + "subtractions. On the lists used by the theorem, 3<=i<=k+3 and "
                + "the indices descend, so the displayed gaps are the exact "
                + "nonnegative numbers of intervening R calls."),
            Definition("compile", "The public compiler", Compile(),
                "W(H,k,c)=compile(H,k,c)=E(k,Z(H,c)). Its inputs are public natural "
                + "numbers, and its output is an explicit finite Boolean list. It uses "
                + "the computable Nat.find and Nat.zeckendorf constructions and "
                + "structural list recursion. No classical choice of a test tree, "
                + "source coordinate, entry residue, reset, inverse service or "
                + "factorial-period word enters this definition."),
            Describe.Lean(DescribeId.Create("effective-short-compiler"),
                DeclarationHandle.Create(Prefix + "effective_short_compiler"),
                H("Both directions and every shifted terminal reply"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every H>1, K is exactly the original least "
                        + "positive direction. For either k=K or k=K+1, and every "
                        + "natural requested shift c, Z is descending, each index "
                        + "lies between 3 and K+3, and its Fibonacci sum is t(H,c). "
                        + "The emitted word has exactly k replacements and exactly "
                        + "length(Z) grafts, at most Gamma(H). Every actual natural "
                        + "pair satisfies the integer endpoint-quantity identity "
                        + "and the shifted terminal gcd identity displayed below. "
                        + "Thus all representatives of every residue shift are "
                        + "covered by the same public compiler.")),
                    Paragraph(Text("The existing Zeckendorf theorem supplies the "
                        + "finite sum and nonadjacency. Since t-2<H<=fib(K+4), "
                        + "each occupied index is at most K+3. After removing index "
                        + "2 the remaining indices range from 3 to K+3 with gaps "
                        + "at least two, hence their number is at most "
                        + "floor((K+2)/2). Appending one index gives the graft bound. "
                        + "When index 2 was present, index 3 was absent, so appending "
                        + "4 preserves descending order. Otherwise appending 3 does. "
                        + "This also covers K=1, the empty representation and the "
                        + "offsets zero and one.")),
                    Paragraph(Text("An emitted graft with index i has exactly i-3 "
                        + "replacements remaining after it. The existing original "
                        + "quantity law gives q R^(i-3)(1,0)=fib(i). Induction on "
                        + "the descending weight list proves the actual integer "
                        + "quantity identity and makes the replacement counts "
                        + "telescope to k. Reduction of t modulo H then gives the "
                        + "complete gcd reply. All prefixes are actual applications "
                        + "of R and G to natural pairs; zero is in the same domain. "
                        + "The direction K+1 adds an initial replacement while "
                        + "preserving every graft's remaining replacement count.")),
                    Paragraph(Text("The compiler produces a word for a caller to "
                        + "execute serially on its retained source handle, consuming "
                        + "each fixed acknowledgement before the next call. Its "
                        + "correctness holds for every current integer entry, so a "
                        + "later acquisition scheduler can invoke it at any cut "
                        + "having the required residue. The separately paid current "
                        + "gcd port, exclusive source control, authentic binding and "
                        + "rights, service completion and sufficient finite backing "
                        + "remain premises of actual execution. This result supplies "
                        + "no hardware realization or source-service price.")),
                    Paragraph(Text("The effective common-direction digit and CRT "
                        + "scheduler, its earned reply tape, positive closing "
                        + "trajectory, same-run totals, entry decoder and installed "
                        + "synchronized continuation are separate constructions. "
                        + "No bit-work, bit-space or total-resource optimum is "
                        + "asserted here. Local binary input handling, arithmetic, "
                        + "word storage and emission, acknowledgements, source "
                        + "services and backing must still be charged in the full "
                        + "acquisition contract."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
             "D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost")),
         DocumentEdge.Dependency.Create(GidRef.Create(
             "D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling")),
         DocumentEdge.Dependency.Create(GidRef.Create(
             "D5/S3/Analytic/GoldenEulerBetaZeckendorf")),
         DocumentEdge.Dependency.Create(GidRef.Create(
             "D5/S1/Digit/GoldenZeckendorfLanguage"))]));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("positive-probe-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Sub(Formula x, Formula y) => Par(Seq(x, Minus, y));
    private static Formula LeOf(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula And(params Formula[] fs) => Join(Land, fs);
    private static Formula Or(Formula a, Formula b) => Join(Lor, [a,b]);
    private static Formula Join(Formula token, Formula[] fs)
    {
        var result = fs[0];
        for (var i = 1; i < fs.Length; i++) result = Seq(result, Sp, token, Sp, fs[i]);
        return Par(result);
    }
    private static Formula All(string x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, V(x), Sp, InMacro, Sp, type, Comma, Sp, body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula N => C("Nat");
    private static Formula K => C("K", V("H"));
    private static Formula T => C("t", V("H"), V("c"));
    private static Formula Z => C("Z", V("H"), V("c"));
    private static Formula W => C("W", V("H"), V("k"), V("c"));
    private static Formula Fib(Formula n) => C("fib", n);
    private static Formula Direction() => All("H", N,
        EqOf(K, C("min", C("positiveFibDirections", V("H")))));
    private static Formula Bound() => All("H", N, EqOf(C("Gamma", V("H")),
        Add(D(1), C("floorDiv", Add(K, D(2)), D(2)))));
    private static Formula Lift()
    {
        var d = C("mod", V("c"), V("H"));
        var nonzero = C("ite", EqOf(d, D(1)), Add(V("H"), D(1)), d);
        return All("H", N, All("c", N, EqOf(T, C("ite", EqOf(d, D(0)), D(0), nonzero))));
    }
    private static Formula Weights()
    {
        var z = C("zeckendorf", Sub(T, D(2)));
        var last = C("ite", C("containsTwo", z), D(4), D(3));
        var nonzero = C("append", C("filterNotTwo", z), C("singleton", last));
        var test = EqOf(C("mod", V("c"), V("H")), D(0));
        return All("H", N, All("c", N, EqOf(Z, C("ite", test, C("nil"), nonzero))));
    }
    private static Formula Emit() => And(
        All("k", N, EqOf(C("E", V("k"), C("nil")), C("repeatR", V("k")))),
        All("k", N, All("i", N, All("l", C("ListNat"),
            EqOf(C("E", V("k"), C("cons", V("i"), V("l"))),
                C("append", C("repeatR", Sub(V("k"), Sub(V("i"), D(3)))),
                    C("consG", C("E", Sub(V("i"), D(3)), V("l")))))))));
    private static Formula Compile() => All("H", N, All("k", N, All("c", N,
        EqOf(W, C("E", V("k"), Z)))));
    private static Formula Result()
    {
        var qv = C("q", C("iterateR", V("k"), V("v")));
        var terminal = C("q", C("Run", W, V("v")));
        var endpoint = All("v", C("NatPair"), And(EqOf(terminal, Add(qv, T)),
            EqOf(C("gcd", terminal, V("H")), C("gcd", Add(qv, V("c")), V("H")))));
        var indices = All("i", N, Imp(C("member", V("i"), Z),
            And(LeOf(D(3), V("i")), LeOf(V("i"), Add(K, D(3))))));
        var properties = And(C("descending", Z), indices,
            EqOf(C("sumFib", Z), T), EqOf(C("countR", W), V("k")),
            EqOf(C("countG", W), C("length", Z)),
            LeOf(C("countG", W), C("Gamma", V("H"))), endpoint);
        var directions = Or(EqOf(V("k"), K), EqOf(V("k"), Add(K, D(1))));
        var compiler = All("k", N, All("c", N, Imp(directions, properties)));
        var eligible = And(LeOf(D(1), V("j")), LeOf(V("H"), Fib(Add(V("j"), D(4)))));
        var least = All("j", N, Imp(eligible, LeOf(K, V("j"))));
        var all = And(LeOf(D(1), K), LeOf(V("H"), Fib(Add(K, D(4)))), least, compiler);
        return All("H", N, Imp(Seq(D(1), Sp, Lt, Sp, V("H")), all));
    }
}
