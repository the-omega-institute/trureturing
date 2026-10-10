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
            Paragraph(Text(
                "Window is the existing five-letter alphabet. Its null, low, high, ends and middle letters have "
                + "printed low-to-high bits 000, 100, 001, 101 and 010. The existing reader processes windows in "
                + "the order of the list, rejects when the prior seam and the current high bit are both true, and "
                + "otherwise replaces the seam by the current low bit. Its clock is three Fibonacci steps "
                + "S(a,b)=(a+2b,2a+3b), and its quantity is q(a,b)=2a+3b. At modulus zero its coefficient carrier "
                + "is the integers, with no reduction.")),
            Paragraph(Text(
                "This application is one scoped adapter for the author-owned analysis interface. Any theorem "
                + "kind may supply a typed contract faithfully tied to its own original source occurrence; neither "
                + "the name nor the proposition type of native_execution defines generic eligibility. The generic "
                + "contract must preserve universes, the full dependent telescope and implicit, instance and proof "
                + "context, and identify the actual source, readouts, selected task and layers. Positive proof escape, "
                + "positive information gain, finite states, an acquired probability law and Fibonacci semantics "
                + "are not conditions for representing an analysis contract. These are interface obligations, not "
                + "a compiled universal source bridge or a theorem assigning Fibonacci semantics to every theorem. "
                + "Analysis does not complete or certify ordinary four-slot Registration. Direct source registration "
                + "keeps its complete DependentFamily evidence in realization and familyRecord=none; a nonempty "
                + "familyRecord belongs only to the existing finite catalog / LegacyPrimitiveRealization adapter "
                + "with its finite bridge. The ordinary registration obligations and statuses retain their scope.")),
            Paragraph(Text(
                "For the initialized single-window application, the source is the complete five-letter Window "
                + "type. The initial seam is false and the composition is (0,0). The first state is "
                + "rawTransition(rawMachine(0).start,a), exactly rawMachine(0).toDFA.eval([a]); its seam is "
                + "first(a) and its composition is residue(0,bitComposition(a)). This is the singleton-word "
                + "application of native_execution with s=false, c=(0,0) and w=[a], for every a:Window. The "
                + "original theorem still ranges over both seams, all natural initial compositions and all finite "
                + "words, and retains its error equivalence and every candidate successful-state equivalence. "
                + "The finite application does not replace that telescope or claim counts for its full domain. "
                + "The middle bit excludes both endpoint bits, while the ends "
                + "letter occupies low 2 and high 5 together, with no additional position.")),
            Paragraph(Text(
                "Continue with the existing high letter on that same first state. The reached state is "
                + "rawMachine(0).toDFA.eval([a,high]), and rawOutput gives the total Option integer reply, "
                + "including none. In the order null, low, high, ends, middle, the first quantities are 0,2,5,7,3 "
                + "and the continuation replies are some(5),none,some(26),none,some(18). The first quantity is "
                + "injective on this alphabet. The guard for the suffix is the complement of the first state's "
                + "seam; low and ends reject, and the rejection remains part of the total output domain. This is "
                + "not the low-to-high LiteralWindowEnd execution or an appended-null suffix.")),
            Paragraph(Text(
                "Let p be any nonnegative real five-mode law with total mass one. A is the parity record that the "
                + "first actual integer reply is odd. It consists exactly of high, ends and middle, with mass "
                + "m=Y+Z, where X=p(low)+p(ends), Y=p(high)+p(ends), Z=p(middle), kappa=p(ends) and r=1-Z. On the "
                + "same realization, A together with a rejected high suffix is exactly the ends event, whose target "
                + "indicator has four-corner coefficient J=1. Without conditioning, rejection has mass X and J=0.")),
            Paragraph(Text(
                "For m>0 the conditional next-reply law assigns masses Z/m, (Y-kappa)/m and kappa/m to some(18), "
                + "some(26) and none, respectively, and zero to every other Option integer reply. These masses are "
                + "nonnegative and sum to one, including when some letters have zero mass. For both r>0 and m>0, "
                + "subtracting the prediction under the product completion kappa*=X*Y/r gives rejection residual "
                + "Delta/(r*m), where Delta=r*kappa-X*Y. The product completion is a legal law by the normalized "
                + "Boolean coupling application. No assumption of strict positivity of individual cells is used. "
                + "When m=0 there is no conditional law on A. When r=0 the source is the unique middle law, A has "
                + "mass one and the next reply is some(18); no expression with division by r is used.")),
            Paragraph(Text(
                "A finite actual source Omega with normalized real mass q and window map a pushes forward to p by "
                + "summing q over each atom fiber. PushforwardComposition.pushforward_comp and sum_indicator_comp "
                + "identify the source low, high and middle events with X,Y,Z and the source joint parity/reply "
                + "table with the table computed from p. Dividing that joint table by the same positive "
                + "parity-event mass gives the conditional distribution above. Thus the response concerns one "
                + "source, its actual first record and its actual same-state continuation. It does not combine "
                + "separately attainable marginal laws.")),
            Paragraph(Text(
                "For coarse coordinates X=Y=2/5 and Z=1/5, the legal completions kappa=1/10 and 3/10 give "
                + "Delta=-2/25 and 2/25. Both laws give positive mass to every letter and the same parity-event "
                + "mass 3/5, but conditional rejection probabilities 1/6 and 1/2. Exact first-reply laws identify "
                + "the complete atom law because the five first replies are distinct. One observed reply identifies "
                + "only that sample letter: either of these laws can produce it. A nonempty finite archive supplies its "
                + "empirical law and empirical determinant, with no certification of an unknown source law absent a "
                + "sampling contract. A single-window atom law gives no cross-window joint relation, and the bottom "
                + "determinant is not the directed native seam-transfer determinant. No information gain, proof "
                + "escape or scalar score follows merely from this response identity.")),
            Paragraph(Text(
                "For the micro analysis in this adapter, State is the complete Window alphabet, including letters "
                + "of zero probability. The atom is a itself, with modeIndex as an injective code; seam is "
                + "some(first(a)), and guard is the complement of first(a). "
                + "and reply is the actual total high-suffix reply above. These maps, not an unrelated five-row "
                + "table, define the joint readout kernel. The generic finite consumer requires a complete "
                + "duplicate-free actual-state enumeration, or an equivalent finite presentation, with proofs "
                + "that every table kernel agrees in both directions with these actual readouts. Reported values "
                + "and selected task outputs additionally require exact decoding correspondence. An initial "
                + "readout bundle and each later addition must refer to these same states and maps. The existing "
                + "LayerChain interface allows a nontrivial initial kernel and equal adjacent kernels; initial "
                + "capture and collapsed layers remain in the spectrum, and final unresolved pairs remain separate. "
                + "In particular guard after seam is a collapsed layer. Ordered unequal pairs use N(N-1), with "
                + "N=5 here, irrespective of probability support. This count concerns Window, not an arbitrary "
                + "source Omega that pushes forward to Window. A restriction, parameter fiber or quotient must "
                + "be explicit and proved to preserve the selected readouts and task within its stated scope; "
                + "its count cannot be substituted for the original domain's count.")),
            Paragraph(Text(
                "StructuralArena and StructuralCatalog supply arbitrary-state kernels; DependentFamily supplies "
                + "dependent parameter/state/output types, while its ordinary Registration separately requires "
                + "variation, sensitivity and actual observational dependence. Those latter requirements are not "
                + "universal analysis eligibility conditions. Finite acquisition reuses Counting's "
                + "Arena.StateEnumeration and the FusedCorrectness declarations fusedFull_eq_escapeNumerator, "
                + "fusedUnique_eq_uniqueCaptureCount and fusedWithout_eq_escapeNumerator_without; generated "
                + "extensional kernels and layeredCapture_partition retain their existing hypotheses. Their use "
                + "requires each client's source and table reflection proofs, not a new bind-only theorem. "
                + "A probability law and its same-source pushforward are needed for the macro and conditional "
                + "readings, not for unweighted micro counts. An absent law leaves its law statistics unknown; "
                + "missing or unsupported acquisition evidence makes the affected reading unavailable; a finite "
                + "pair rate on an infinite or at-most-singleton domain, or a conditional law on a zero-mass "
                + "event, is not applicable. These distinctions are per-reading explanations, not audit statuses. "
                + "The generic interface and client acquisition obligations require their own compiled evidence; "
                + "the existing native proofs and this application exposition do not establish that implementation.")),
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
                    Paragraph(Text(
                        "R(s,c,w) abbreviates the existing rawMachine(0).toDFA.evalFrom(some(s,residue(0,c)),w). The map "
                        + "residue(0,d) is the coordinatewise natural-to-integer cast. The formula includes both the error "
                        + "equivalence and the equivalence for every candidate successful seam and integer composition.")),
                    Paragraph(Text("Word induction identifies the actual guard with bit legality. The natural bit contributions cast to the existing reader's five displacements, and three natural Fibonacci steps cast to its clock. A rejected prefix remains error for every remaining letter. A successful prefix therefore has natural coordinates following the displayed source recurrence; conversely each such source history realizes that same successful state. The assertion holds for every natural initial composition and either incoming seam."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-null-fiber-zero"),
                DeclarationHandle.Create(Prefix + "null_reply_zero_iff"), H("The exact zero fiber of actual null continuation"),
                StatementSource.FromAuthor(ZeroFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "task(0,w) is the existing immediate output from seam false and composition (0,0). The appended "
                        + "letter is the existing zero window. Its guard is always legal on a live state, it sets the seam "
                        + "to false, and it performs the full clock before returning qS(c)=8a+13b on a natural composition "
                        + "c=(a,b). It leaves error absorbing.")),
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
