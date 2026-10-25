using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class CommonDirectionSchedulerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform digit controller combines prime-power tests into common-direction "
            + "positive experiments and retains their complete scalar replies.",
        H("Effective common-direction digit scheduling"),
        Blocks(
            Paragraph(Text("Fix a public natural modulus H>=1 and an arbitrary natural pair "
                + "v=(a,b), including zero. The original chronological calls are R(a,b)=(b,a+b) "
                + "and G(a,b)=(a+1,b); true means R in TerminalGcdAcquisitionCost.runWord. "
                + "Write q(a,b)=2a+3b, K=PositiveProbeCompiler.direction(H), "
                + "Gamma=PositiveProbeCompiler.graftBound(H), and "
                + "B=max over p dividing H of factorization(H,p)*(p-1). "
                + "An experiment word precedes a separately paid current gcd read. "
                + "The reply is the whole natural number gcd(q(current),H).")),
            Def("Axis", "A finite digit record", C("Axis", C("Nat"), C("Nat"), C("Nat")),
                "For a prime power p^e, a record (s,r,d) consists of a completed digit "
                + "level, its prefix residue, and the trial digit. Initially it is (0,0,0). "
                + "Its center is r+p^s*d. The proof invariant for the unknown scalar n is "
                + "s<=e, r=n mod p^s, 0<=d<p-1, and d<=floor(n/p^s) mod p. "
                + "The natural rank is (e-s)*(p-1)-d."),
            Def("advance", "Advance from the full reply", Advance(),
                "Completed records stay fixed. Otherwise divisibility of the complete "
                + "reply g by p^(s+1) accepts the center as the next prefix and resets "
                + "the trial to zero. A failed test increments d when another tested "
                + "digit remains. After all p-1 failures the last digit p-1 is inferred, "
                + "the prefix is extended, and the trial resets. Each active update "
                + "strictly decreases the rank; accepting a low trial can decrease "
                + "it by more than one. No valuation or Boolean answer replaces g."),
            Def("shift", "One computable CRT shift", Shift(),
                "For each unfinished axis request the negative of its trial center "
                + "modulo p^e; for a finished axis request the negative of its recovered "
                + "residue. Compatible(H,a,c) means that desired(p,a)+c is divisible "
                + "by p^e at every prime divisor. The algorithm searches 0,...,H-1 "
                + "for the first compatible shift. The existing ZMod CRT equivalence "
                + "proves that this bounded search succeeds when H>0. The equivalence "
                + "is used only in the correctness proof; the computation is the "
                + "finite search. No polynomial local-work bound is attached to it."),
            Def("rounds", "Chronological full-reply execution", Rounds(),
                "A round computes c from the current finite table, receives g from "
                + "the reply interface, advances every axis from that same g, and "
                + "records (c,g) before the recursively generated suffix. After B "
                + "rounds every prime-power residue is complete. Completed axes remain "
                + "valid during padding rounds. Negating a final compatible shift "
                + "in ZMod H reconstructs n modulo H. Thus all axes finish with "
                + "B paid scalar replies, rather than a sum of their budgets."),
            Def("schedule", "The two public directions", Schedule(),
                "The same local digit policy runs first at direction K and then at "
                + "direction K+1. The output contains both recovered scalars and the "
                + "chronological concatenation of triples (k,c,g). For H=1 both "
                + "stages return zero with an empty tape. The controller takes only "
                + "H and incoming replies; it never takes a hidden source coordinate. "
                + "compiledReply(H,v,k,c) is the mathematical interpreter obtained "
                + "by executing the actual compiler word at v and reading its gcd. "
                + "It is not a local primitive supplied to the controller."),
            Def("decode", "An explicit earned entry residue", Decode(),
                "The two consecutive quantity rows have matrix [[2,3],[3,5]]. "
                + "Apply its integer inverse [[5,-3],[-3,2]] in ZMod H, then apply "
                + "the inverse of the public residue replacement permutation to "
                + "the K-th power. The resulting pair is the entry residue. This "
                + "is a computation on the two earned scalars, not a hidden label."),
            Describe.Lean(DescribeId.Create("effective-common-direction-scheduler"),
                DeclarationHandle.Create(Prefix + "effective_scheduler"),
                H("All natural sources and the complete reply tape"),
                StatementSource.FromAuthor(Effective()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every H>=1 and every actual natural pair v, "
                        + "the decoded output is residueSource(H,v). The two scalar "
                        + "outputs are q(R^K(v)) and q(R^(K+1)(v)) in ZMod H. "
                        + "The tape has zero entries when H=1 and exactly 2B otherwise. "
                        + "Every triple has k in {K,K+1}, c<H, exactly k actual R "
                        + "calls and at most Gamma actual G calls in its compiler "
                        + "word, and its retained g equals both the original complete "
                        + "terminal gcd and gcd(q(R^k(v))+c,H).")),
                    Paragraph(Text("Digit correctness uses Nat.mod_pow_succ to split "
                        + "a prefix and its next digit. Since p^(s+1) divides H, "
                        + "its divisibility in gcd(n+c,H) is equivalent to the next "
                        + "prefix matching the center. The rank decreases on every "
                        + "unfinished axis; its initial value is e*(p-1)<=B. "
                        + "A finite induction therefore completes all axes at once. "
                        + "CRT injectivity reconstructs the scalar. The concrete "
                        + "PositiveProbeCompiler.effective_short_compiler supplies "
                        + "the actual word, its two action counts, and the exact "
                        + "full terminal reply identity for every natural source. "
                        + "Finally the inverse scalar rows and the residue replacement "
                        + "permutation recover the entry pair.")),
                    Paragraph(Text("The reply-interface interpretation requires an "
                        + "actual cut of the same retained handle before each experiment. "
                        + "At that cut the current residue must equal the entry residue. "
                        + "Execute compile(H,k,c) in its listed chronological order, "
                        + "consume each fixed acknowledgement, perform one paid full "
                        + "current gcd read, close by positive original actions back "
                        + "to the required residue, and commit the local table before "
                        + "the next callable cut. ClosingCut states the residue and "
                        + "complete-reply equalities required at an experiment cut. "
                        + "Constructing those positive closing words, their least "
                        + "period, and their actual concatenated action tape is a "
                        + "separate obligation; the present two-stage tape is a tape "
                        + "of requested experiments and replies.")),
                    Paragraph(Text("Same-run counting must relate each requested "
                        + "triple to exactly one actual read and include every closing "
                        + "action. In the original notation its target equalities are "
                        + "Q=T0+T1, NR=L_H*(K*T0+(K+1)*T1), and "
                        + "NG=H*sum(g_j), followed by the stated bounds Q<=2B, "
                        + "NR<=L_H*(2K+1)*B and NG<=2H*Gamma*B. These equalities, "
                        + "the integer affine endpoint and every-prefix growth bounds "
                        + "do not follow merely from compiler-word counts. An installed "
                        + "continuation must additionally preserve the immutable earned "
                        + "entry and a separately synchronized current residue after "
                        + "each action, acknowledgement and local commit. No such "
                        + "closing or synchronized continuation is asserted here."))), DescribeRole.Theorem),
            Def("binaryRounds", "Finite binary local control", BinaryRounds(),
                "Encode each natural local field and every complete reply with "
                + "Nat.digits 2, least significant digit first; zero has the empty "
                + "encoding. A finite association list has one binary triple per "
                + "public prime-factor key. decodeJoint looks up that finite table. "
                + "binaryShift emits the binary encoding of the bounded CRT shift; "
                + "binaryAdvance decodes the full incoming reply and commits the "
                + "next encoded table. binaryRounds iterates these operations by "
                + "structural recursion with an explicit finite round count."),
            Describe.Lean(DescribeId.Create("finite-binary-common-direction-execution"),
                DeclarationHandle.Create(Prefix + "finite_binary_execution"),
                H("The binary refinement preserves every finite execution"),
                StatementSource.FromAuthor(BinaryResult()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every public H, every total scalar reply "
                        + "function, every finite j and every local table, binaryRounds "
                        + "on encoded inputs equals the encoded numeric execution, "
                        + "including its entire ordered shift/reply tape. Decoding "
                        + "an encoded table is exact, the table length is the number "
                        + "of prime divisors, and every encoded digit is below two. "
                        + "There is no positivity restriction on replies or source "
                        + "coordinates. The all-horizon identity applies in particular "
                        + "to both B-round stages with the actual compiler replies.")),
                    Paragraph(Text("Nat.ofDigits_digits gives exact field and reply "
                        + "round trips. Finite-table lookup recovers the encoded "
                        + "record for each public prime key. The local binary update "
                        + "therefore commutes with the numeric update, and induction "
                        + "on j transports the entire chronological execution. "
                        + "This proves a finite effective representation. It supplies "
                        + "no numerical bit-work or bit-space bound. Factoring H, "
                        + "bounded shift search, binary arithmetic, word emission, "
                        + "tape storage, service work and backing are still charged "
                        + "resources under the original public finite-computation "
                        + "premises. Only paid reads are optimized."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost"))]));

    private static DocumentBlock Def(string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create("common-direction-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(f),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => Call(s, a);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Sp, InMacro, Sp, t, Comma, Sp, b);
    private static Formula And(params Formula[] a)
    {
        var r = a[0];
        for (var i = 1; i < a.Length; i++) r = Seq(r, Sp, Land, Sp, a[i]);
        return Seq(Open, r, Close);
    }
    private static Formula Advance() => EqOf(C("advance", V("p"), V("e"), V("a"), V("g")),
        C("digitUpdate", V("p"), V("e"), V("a"), V("g")));
    private static Formula Shift() => EqOf(C("shift", V("H"), V("a")),
        C("firstCompatibleBelow", V("H"), V("a")));
    private static Formula Rounds() => EqOf(C("rounds", V("H"), V("answer"), V("j"), V("a")),
        C("iterateFullReply", V("j"), V("a")));
    private static Formula Schedule() => EqOf(C("schedule", V("H"), V("answer")),
        C("twoStages", C("K", V("H")), C("B", V("H")), V("answer")));
    private static Formula Decode() => EqOf(C("decode", V("H"), V("y")),
        C("inverseResidueDirection", C("K", V("H")),
            C("inverseQuantityRows", V("y"))));
    private static Formula Effective() => All("H", C("Nat"), All("v", C("NatPair"),
        Seq(C("positive", V("H")), Sp, Implies, Sp,
            And(EqOf(C("decodedSchedule", V("H"), V("v")), C("residue", V("H"), V("v"))),
                EqOf(C("scalars", V("H"), V("v")), C("consecutiveQuantities", V("H"), V("v"))),
                EqOf(C("tapeLength", V("H"), V("v")), C("readBudget", V("H"))),
                C("allActualCompilerTriples", V("H"), V("v"))))));
    private static Formula BinaryRounds() => EqOf(C("binaryRounds", V("H"), V("answer"), V("j"), V("b")),
        C("iterateBinaryFullReply", V("j"), V("b")));
    private static Formula BinaryResult() => All("H", C("Nat"), All("answer", C("NatToNat"),
        All("j", C("Nat"), All("a", C("Joint", V("H")),
            And(EqOf(C("binaryRunEncoded", V("H"), V("answer"), V("j"), V("a")),
                    C("encodeNumericRun", V("H"), V("answer"), V("j"), V("a"))),
                EqOf(C("decodeEncode", V("H"), V("a")), V("a")),
                EqOf(C("encodedTableLength", V("H"), V("a")), C("primeFactorCount", V("H"))),
                C("allDigitsBelowTwo"))))));
}
