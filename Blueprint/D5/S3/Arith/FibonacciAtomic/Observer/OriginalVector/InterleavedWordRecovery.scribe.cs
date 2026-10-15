using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector;
internal sealed class InterleavedWordRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "InterleavedWordRecovery", H("Original vector recovery by a complete legal word"), Blocks(
            Entry("original", "Complete promised source family", "The cut is the entire level of addresses of length m = clog 2 h, including unselected leaves. At selected address q i numerical false is original zero, hence source alpha (true); numerical true is original one, hence source beta (false). Every unselected leaf is alpha. The ordered injective selection and complete skeleton are common promised input, rather than acquired shape evidence. Every full vector is allowed, including all-alpha sources outside the alpha orbit. At h = 1 the root is the selected leaf.", DescribeRole.Definition),
            Entry("program", "Native Q, U and Z table", "Q s reads q at index length s followed by length s divided by two right steps. At even epochs alpha and beta decode to zero and one; at odd epochs beta and branch decode to zero and one. The total four-valued response table holds Q s for unsupported replies, including absence. A supported Read appends one bit and enters U s or the final Z s. U s performs exactly one genuine substitution on the same source and enters Q s. Z s halts with its fixed full vector. The initial vertex is Q empty for every source.", DescribeRole.Definition),
            Entry("encode", "Alternating block level coordinates", "For each zero-based Read index i, coordinates 5i and 5i+1 record zero and one. Coordinate 5i+3 records the following Update, when present. Coordinates of residues two and four remain zero. Earlier blocks stay activated and later blocks stay zero. The final Read block has no following separator or Update. The exact width is 5h-3. This is the source's explicit level-coordinate construction, an application of the classical Havel–Moravek method, rather than an independent graph-theory result.", DescribeRole.Definition),
            Entry("Installed", "Exact installed image", "Installed h consists precisely of encode applied to all Q, U and Z vertices. No ambient word has an instruction row. The inverse is an immutable table lookup. It does not introduce a persistent decoded vertex.", DescribeRole.Definition),
            Entry("wordProgram", "Word-only row selection", "The only mutable controller argument is one Installed word. Its row chooses the instruction, materialized literal, immediate response word and fixed full output. Source, prefix support, epoch, rank and trace are proof coordinates and are unavailable to row selection. The proof uses NativeSerialMachine.Run and nativeStep for both representations, preserving the same physical source, chronological raw replies, source successors and first full Halt.", DescribeRole.Definition),
            Paragraph(Text("In the formula, m abbreviates clog 2 h; FullVectors h is the subtype of Boolean lists of length h; u x abbreviates original m q x; T x abbreviates chronology q 0 x; Q, U and Z omit proof-irrelevant bound fields. E is encode, I is install, J is inverse, and liftConfig changes only the vertex to its installed word. readCount is the length of answers; updateCount counts update events; Reached is nativeStep reachability from the common initial vertex, epoch zero, the original source and empty trace. ReachedVertices is the subtype of vertices for which some current register is actually reached from the fixed original u x. The displayed word reachability uses the corresponding installed initial word. These notations denote the actual definitions, not additional hypotheses or execution certificates.")),
            Describe.Lean(DescribeId.Create("interleaved-word-recovery"),
                DeclarationHandle.Create(Prefix + "interleaved_word_recovery"),
                H("Full native recovery and exact word realization"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The complete family construction uses ActualCutPartitionRecovery.prefixTrie and its original prefixTrie_at theorem. NativeDepthPatterns.original_present_transport and the unrestricted append-readout component of ActualLeafHistoryRigidity.actual_address_geometry preserve navigation. DelayedOriginalReadout.right_clock_iterate and right_clock_readout supply the reply clocks and genuine-update witness. NativeSerialDepth.run_unique supplies labeled trace and output uniqueness. Pinned finite-cardinality and Hamming facts normalize the resulting exact counts; admissibility uses AdmissibleCount.Adm and ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true.")),
                    Paragraph(Text("The new inference constructs the source-independent table and its actual native Run, proves both directions of actual Q/U/Z supports, and realizes exactly their installed legal image. Every allowed prefix has a promised completion, including every unary Update position and every fixed full-output halt. The installed union has 3 times 2 to h minus 3 states; one source visits exactly 2h states. Each supported primitive changes exactly one word bit, unsupported replies hold, and the first full Halt immediately follows the final primitive with no local step or intermediate output.")),
                    Paragraph(Text("This is conditional mathematical installation under Definition 1.3's initialization, immutable lookup, literal delivery, native primitive execution, immediate response-write and fixed full-output services. It establishes neither their physical availability nor free setup. It asserts no optimal total cost or minimum width. The old and classical widths and U(h), arbitrary-competitor Read lower bound, Fibonacci and Theta(h) claims, literal/union/service bills and the whole parent theorem remain outside this result. The word execution clause is this explicit code instance; the generic obligations for arbitrary chosen codes in Verification 4.3 are not claimed."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("interleaved-word-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement() => All("h", V("Nat"), Imp(Lt(D(0), V("h")),
        All("q", Arr(Call("Fin", V("h")), V("Address")), Imp(Call("Injective", V("q")),
            Imp(All("i", Call("Fin", V("h")), EqOf(Len(Call("q", V("i"))), M())), Body())))));

    private static Formula Body() => And(
        Call("Injective", Lam("x", Call("FullVectors", V("h")), Orig(Call("value", V("x"))))),
        All("x", Bools(), All("a", V("Address"), Imp(And(EqOf(Len(V("a")), M()), All("i", Call("Fin", V("h")), Ne(Call("q", V("i")), V("a")))), EqOf(Call("subtree", V("a"), Orig(V("x"))), Call("some", Call("alpha")))))),
        All("x", Bools(), All("i", Call("Fin", V("h")), EqOf(Call("subtree", Call("q", V("i")), Orig(V("x"))), Call("some", Call("of", Call("not", Call("getD", V("x"), Call("value", V("i")), V("false")))))))),
        All("x", Bools(), Imp(EqOf(Len(V("x")), V("h")), And(RunAt(false, Trace("x"), V("x")), RunAt(true, Trace("x"), V("x")), All("t", V("Trace"), All("z", Bools(), Imp(RunAt(true, V("t"), V("z")), And(EqOf(V("t"), Trace("x")), EqOf(V("z"), V("x")))))), EqOf(Call("readCount", Trace("x")), V("h")), EqOf(Len(Trace("x")), Height()), EqOf(Call("updateCount", Trace("x")), Sub(V("h"), D(1))), Seq(Call("localStep"), Sp, Neg, Sp, InMacro, Sp, Trace("x")), EqOf(Call("card", Call("ReachedVertices", V("h"), V("q"), V("x"))), Mul(D(2), V("h")))))),
        All("x", Bools(), Imp(EqOf(Len(V("x")), V("h")), All("v", Vertices(), All("r", V("Source"), Equ(Call("Reached", V("q"), Orig(V("x")), V("v"), V("r")), And(Call("Fits", V("v"), V("x")), EqOf(V("r"), Root(Call("epochOf", V("v")))))))))),
        EqOf(Call("card", Vertices()), N()),
        EqOf(Call("card", Words()), N()),
        All("w", Words(), Call("Adm", Width(), Call("value", V("w")))),
        Call("Injective", Call("encode", V("h"))),
        All("s", Bools(), Imp(Lt(Len(V("s")), V("h")), All("b", V("Bool"), EqOf(Distance(Code(Q()), Code(Call("child", V("s"), V("b")))), D(1))))),
        All("s", Bools(), Imp(UpdateBound(), EqOf(Distance(Code(U()), Code(Q())), D(1)))),
        All("s", Bools(), Imp(Lt(Len(V("s")), V("h")), All("r", V("Reply"), Imp(EqOf(Call("decode", Len(V("s")), V("r")), Call("none")), And(EqOf(Response(), Q()), EqOf(Distance(Code(Q()), Code(Response())), D(0))))))),
        All("w", Words(), Some("x", Bools(), And(EqOf(Len(V("x")), V("h")), Some("e", V("Nat"), Some("r", V("Source"), Some("t", V("Trace"), WordReached())))))),
        All("s", Bools(), Imp(Lt(Len(V("s")), V("h")), EqOf(Call("wordProgram", V("q"), Installed(Q())), Call("Read", Call("literal", V("q"), Len(V("s"))), Lam("r", V("Reply"), Installed(Response())))))),
        All("s", Bools(), Imp(UpdateBound(), EqOf(Call("wordProgram", V("q"), Installed(U())), Call("Update", Installed(Q()))))),
        All("s", Bools(), Imp(EqOf(Len(V("s")), V("h")), EqOf(Call("wordProgram", V("q"), Installed(Call("Z", V("s")))), Call("Halt", V("s"))))),
        All("w,c", Words(), Ne(Call("wordProgram", V("q"), V("w")), Call("localStep", V("c")))),
        Call("Injective", Lam("x", Bools(), Call("answers", Trace("x")))),
        All("x", Bools(), Imp(EqOf(Len(V("x")), V("h")), All("w", Words(), All("r", V("Source"), Equ(Some("e", V("Nat"), Some("t", V("Trace"), WordReached())), And(Call("Fits", Call("inverse", V("w")), V("x")), EqOf(V("r"), Root(Call("epochOf", Call("inverse", V("w"))))))))))),
        All("v", Vertices(), All("e", V("Nat"), All("r", V("Source"), All("t", V("Trace"), EqOf(Call("nativeStep", Call("wordProgram", V("q")), Config(Installed(V("v")))), Call("map", Call("nativeStep", Call("program", V("q")), Config(V("v"))), Call("liftConfig", V("h")))))))),
        All("x", Bools(), All("a", V("Address"), Imp(EqOf(Len(V("a")), M()), EqOf(Call("subtree", V("a"), Orig(V("x"))), Call("some", Call("leafValue", V("q"), V("x"), V("a"))))))),
        All("u", V("Source"), Ne(Call("substitution", V("u")), V("u"))));

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula All(string ns, Formula t, Formula b) => Bound(Forall, ns, t, b);
    private static Formula Some(string ns, Formula t, Formula b) => Bound(Exists, ns, t, b);
    private static Formula Lam(string ns, Formula t, Formula b) => Bound(LambdaLower, ns, t, b);
    private static Formula Bound(Formula token, string ns, Formula t, Formula b) => Seq(token, Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Equ(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Cdot, Sp, b);
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula Bools() => Call("List", V("Bool"));
    private static Formula Vertices() => Call("Vertex", V("h"));
    private static Formula Words() => Call("Installed", V("h"));
    private static Formula M() => Call("clog", D(2), V("h"));
    private static Formula Height() => Sub(Mul(D(2), V("h")), D(1));
    private static Formula N() => Sub(Mul(D(3), Call("pow", D(2), V("h"))), D(3));
    private static Formula Width() => Sub(Mul(D(5), V("h")), D(3));
    private static Formula Orig(Formula x) => Call("original", M(), V("q"), x);
    private static Formula Trace(string x) => Call("chronology", V("q"), D(0), V(x));
    private static Formula Root(Formula e) => Call("iterate", V("substitution"), e, Orig(V("x")));
    private static Formula Q() => Call("Q", V("s"));
    private static Formula U() => Call("U", V("s"));
    private static Formula Code(Formula v) => Call("encode", v);
    private static Formula Installed(Formula v) => Call("install", v);
    private static Formula Response() => Call("response", V("s"), V("r"));
    private static Formula Distance(Formula a, Formula b) => Call("hammingDist", a, b);
    private static Formula UpdateBound() => And(Lt(D(0), Len(V("s"))), Lt(Len(V("s")), V("h")));
    private static Formula Config(Formula v) => Call("tuple", v, V("e"), V("r"), V("t"));
    private static Formula WordReached() => Call("Reaches", Call("nativeStep", Call("wordProgram", V("q"))),
        Call("tuple", Installed(Call("initial", V("h"))), D(0), Orig(V("x")), Call("emptyTrace")), Config(V("w")));
    private static Formula RunAt(bool word, Formula t, Formula z) => Call("Run",
        Call(word ? "wordProgram" : "program", V("q")), word ? Installed(Call("initial", V("h"))) : Call("initial", V("h")),
        D(0), Orig(V("x")), t, z);
}
