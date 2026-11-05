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
                + "B=costBound(H), the maximum of factorization(H,p)*(p-1) over "
                + "the finite set primeFactors(H), with empty maximum zero. "
                + "An experiment word precedes a separately paid current gcd read. "
                + "The reply is the whole natural number gcd(q(current),H).")),
            Paragraph(Text("In the formulas N denotes the naturals and A(H)=ZMod(H); "
                + "for positive H this is the residue ring modulo H, while A(0) is "
                + "the integers. cast(H,n) is the canonical natural-number cast into "
                + "A(H). PrimeIndex(H) is the subtype of natural primes in "
                + "primeFactors(H); factorization(H,p) is the exponent of its "
                + "underlying natural prime. Joint(H) is the function type "
                + "PrimeIndex(H)->Axis. The definitions below are total for all "
                + "natural parameters, without a validity condition on local records. "
                + "All natural subtractions, including p-1 and the rank, truncate at "
                + "zero; subtraction in a typed A(H) expression is ring subtraction. "
                + "ite(P,x,y) means x if P holds and y otherwise. let binds its "
                + "typed local name in the following expression; a typed mapsto "
                + "expression denotes a function, and constant(X,x) is the "
                + "function on X taking the value x at every argument. fst and snd are product "
                + "projections. Triples associate to the right, except that an "
                + "Axis triple denotes its three-field record constructor; braces "
                + "in the Axis display list the typed fields of that record type. "
                + "List(X) is the type of finite ordered lists of X; nil is the "
                + "empty list, cons prepends, append concatenates left before right, "
                + "map(f,l) applies f in list order, length counts entries, and "
                + "count(w,b) counts occurrences of Boolean b in w.")),
            Def("Axis", "A finite digit record", Axis(),
                "For a prime power p^e, a record (s,r,d) consists of a completed digit "
                + "level, its prefix residue, and the trial digit. Initially it is (0,0,0). "
                + "The field functions level, residue and trial project these three "
                + "natural fields; initialAxis=(0,0,0), and "
                + "center(p,a)=residue(a)+p^level(a)*trial(a). "
                + "The proof invariant for the unknown scalar n is "
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
                + "finite search. In the formula range(H) is the ascending list "
                + "0,...,H-1, decide turns a decidable proposition into its Boolean "
                + "truth value, find(l,f) returns the first element of l satisfying "
                + "f as an option, and getD(o,z) returns that element or the default "
                + "z if the option is empty. This specifies shift even at H=0. "
                + "No polynomial local-work bound is attached to it."),
            Def("rounds", "Chronological full-reply execution", Rounds(),
                "A round computes c from the current finite table, receives g from "
                + "the reply interface, advances every axis from that same g, and "
                + "records (c,g) before the recursively generated suffix. After B "
                + "rounds every prime-power residue is complete. Completed axes remain "
                + "valid during padding rounds. Negating a final compatible shift "
                + "in ZMod H reconstructs n modulo H. Thus all axes finish with "
                + "B paid scalar replies, rather than a sum of their budgets. "
                + "advanceAll(H,a,g) updates each prime record with the same full "
                + "reply: at p it is advance(p,factorization(H,p),a(p),g)."),
            Def("schedule", "The two public directions", Schedule(),
                "The same local digit policy runs first at direction K and then at "
                + "direction K+1. The output contains both recovered scalars and the "
                + "chronological concatenation of triples (k,c,g). For H=1 both "
                + "stages return zero with an empty tape. The controller takes only "
                + "H and incoming replies; it never takes a hidden source coordinate. "
                + "compiledReply(H,v,k,c) is the mathematical interpreter obtained "
                + "by executing the actual compiler word at v and reading its gcd. "
                + "Explicitly, terminalGcd(H,w,v)=gcd(q(runWord(w,v)),H), "
                + "compiledReply(H,v,k,c)=terminalGcd(H,compile(H,k,c),v), "
                + "and recover(H,a)=-cast(H,shift(H,a)). The displayed stage "
                + "equation uses this last definition directly. compile is the "
                + "PositiveProbeCompiler positive Boolean-word compiler; direction "
                + "is its least k>=1 with fib(k+4)>=H, where fib(0)=0 and fib(1)=1, "
                + "and graftBound(H)=1+floor((direction(H)+2)/2). "
                + "runWord executes its list chronologically with true=R and "
                + "false=G. The interpreter is not a local primitive supplied to "
                + "the controller."),
            Def("decode", "An explicit earned entry residue", Decode(),
                "The two consecutive quantity rows have matrix [[2,3],[3,5]]. "
                + "Apply its integer inverse [[5,-3],[-3,2]] in ZMod H, then apply "
                + "the inverse of the public residue replacement permutation to "
                + "the K-th power. The resulting pair is the entry residue. This "
                + "is a computation on the two earned scalars, not a hidden label. "
                + "Here residueReplace(H) is the permutation of A(H) x A(H) "
                + "sending (x,z) to (z,x+z), with inverse (x,z) |-> (z-x,x). "
                + "Its power is composition iterated direction(H) times, and "
                + "inverse denotes the inverse permutation; apply evaluates it. "
                + "All coefficients in decode are cast into A(H)."),
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
                        + "terminal gcd and gcd(q(R^k(v))+c,H). In the formula "
                        + "iterateR(k,v) denotes k iterations of the original R on v, "
                        + "and residueSource(H,v) is its coordinatewise natural cast "
                        + "into A(H) x A(H). The innermost conjunction expands "
                        + "ClosingCut(H,k,c,v,current) into its residue equality and "
                        + "its equality of complete terminal compiler replies.")),
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
                + "structural recursion with an explicit finite round count. "
                + "Precisely, Binary=List(N), BinaryAxis=Binary x Binary x Binary, "
                + "and BinaryJoint(H)=List(PrimeIndex(H) x BinaryAxis). "
                + "digits(n)=Nat.digits(2,n) and ofDigits(c)=Nat.ofDigits(2,c); "
                + "the latter is the sum of c[i]*2^i over list positions, including "
                + "lists with digits above one. encodeAxis(a) applies digits to "
                + "level(a), residue(a), trial(a); decodeAxis applies ofDigits to "
                + "the three fields. encodeJoint(H,a) is the ascending list of "
                + "all public prime keys paired with encodeAxis(a(p)). "
                + "decodeJoint(H,b)(p) decodes the first record with key p in b, "
                + "using (nil,nil,nil) when p is absent. Thus arbitrary binary "
                + "tables, not only encoded valid histories, have a defined meaning. "
                + "binaryShift(H,b)=digits(shift(H,decodeJoint(H,b))) and "
                + "binaryAdvance(H,b,g)=encodeJoint(H,advanceAll(H,decodeJoint(H,b), "
                + "ofDigits(g))). card(primeFactors(H)) counts distinct prime keys."),
            Describe.Lean(DescribeId.Create("finite-binary-common-direction-execution"),
                DeclarationHandle.Create(Prefix + "finite_binary_execution"),
                H("The binary refinement preserves every finite execution"),
                StatementSource.FromAuthor(BinaryResult()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural public H, including H=0, every total scalar reply "
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
    private static Formula Name(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula A => C("A", V("H"));
    private static Formula Joint => C("Joint", V("H"));
    private static Formula Keys => C("PrimeIndex", V("H"));
    private static Formula Binary => Name("Binary");
    private static Formula BinaryJoint => C("BinaryJoint", V("H"));
    private static Formula PairType(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula NatPair => PairType(N, N);
    private static Formula Triple => PairType(N, Par(NatPair));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula ScalarReply => Arrow(N, N);
    private static Formula NumericRun => PairType(Joint, C("List", NatPair));
    private static Formula StageType => PairType(A, C("List", NatPair));
    private static Formula ScheduleType => PairType(Par(PairType(A, A)), C("List", Triple));
    private static Formula BinaryRun => PairType(BinaryJoint, C("List", PairType(Binary, Binary)));
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Tuple(params Formula[] a)
    {
        var r = a[0];
        for (var i = 1; i < a.Length; i++) r = Seq(r, Comma, Sp, a[i]);
        return Par(r);
    }
    private static Formula First(Formula a) => C("fst", a);
    private static Formula Second(Formula a) => C("snd", a);
    private static Formula PlusOf(Formula a, Formula b) => Par(Seq(a, Sp, Plus, Sp, b));
    private static Formula MinusOf(Formula a, Formula b) => Par(Seq(a, Sp, Minus, Sp, b));
    private static Formula TimesOf(Formula a, Formula b) => Par(Seq(a, Sp, Cdot, Sp, b));
    private static Formula Power(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Lam(string s, Formula t, Formula b) =>
        Par(Seq(Par(Seq(V(s), Colon, Sp, t)), Sp, Mapsto, Sp, b));
    private static Formula Constant(Formula t, Formula b) =>
        C("constant", t, b);
    private static Formula Let(string s, Formula t, Formula value, Formula body) =>
        Seq(Name("let"), Sp, V(s), Colon, Sp, t, Sp, Colon, Eq, Sp, value,
            Sp, Name("in"), Sp, Par(body));
    private static Formula And(params Formula[] a)
    {
        var r = a[0];
        for (var i = 1; i < a.Length; i++) r = Seq(r, Sp, Land, Sp, a[i]);
        return Par(r);
    }
    private static Formula Axis() => Seq(Name("Axis"), Sp, Eq, Sp, OpenBrace,
        Name("level"), Colon, Sp, N, Comma, Sp,
        Name("residue"), Colon, Sp, N, Comma, Sp,
        Name("trial"), Colon, Sp, N, CloseBrace);

    private static Formula Advance()
    {
        var s = C("level", V("a"));
        var r = C("residue", V("a"));
        var d = C("trial", V("a"));
        var next = PlusOf(s, D(1));
        var last = Tuple(next, PlusOf(r, TimesOf(Power(V("p"), s), MinusOf(V("p"), D(1)))), D(0));
        var more = C("ite", LtOf(PlusOf(d, D(1)), MinusOf(V("p"), D(1))),
            Tuple(s, r, PlusOf(d, D(1))), last);
        var test = Seq(Power(V("p"), next), Sp, Mid, Sp, V("g"));
        var active = C("ite", test,
            Tuple(next, PlusOf(r, TimesOf(Power(V("p"), s), d)), D(0)), more);
        return All("p", N, All("e", N, All("a", Name("Axis"), All("g", N,
            EqOf(C("advance", V("p"), V("e"), V("a"), V("g")),
                C("ite", LeOf(V("e"), s), V("a"), active))))));
    }

    private static Formula Shift()
    {
        var e = C("factorization", V("H"), V("p"));
        var axis = C("a", V("p"));
        var desired = C("ite", LeOf(e, C("level", axis)), C("residue", axis),
            PlusOf(C("residue", axis), TimesOf(Power(V("p"), C("level", axis)), C("trial", axis))));
        var compatible = All("p", Keys,
            Seq(Power(V("p"), e), Sp, Mid, Sp, PlusOf(desired, V("c"))));
        var search = C("find", C("range", V("H")),
            Lam("c", N, C("decide", C("Compatible", V("H"), V("a"), V("c")))));
        return All("H", N, All("a", Joint, And(
            All("c", N, Seq(C("Compatible", V("H"), V("a"), V("c")), Sp, Iff, Sp, Par(compatible))),
            EqOf(C("shift", V("H"), V("a")), C("getD", search, D(0))))));
    }

    private static Formula Rounds()
    {
        var update = Lam("p", Keys, C("advance", V("p"),
            C("factorization", V("H"), V("p")), C("a", V("p")), V("g")));
        var successor = Let("c", N, C("shift", V("H"), V("a")),
            Let("g", N, C("answer", V("c")),
                Let("t", NumericRun,
                    C("rounds", V("H"), V("answer"), V("j"), C("advanceAll", V("H"), V("a"), V("g"))),
                    Tuple(First(V("t")), C("cons", Tuple(V("c"), V("g")), Second(V("t")))))));
        return All("H", N, And(
            All("a", Joint, All("g", N,
                EqOf(C("advanceAll", V("H"), V("a"), V("g")), update))),
            All("answer", ScalarReply, And(
                All("a", Joint, EqOf(C("rounds", V("H"), V("answer"), D(0), V("a")), Tuple(V("a"), Name("nil")))),
                All("j", N, All("a", Joint,
                    EqOf(C("rounds", V("H"), V("answer"), PlusOf(V("j"), D(1)), V("a")), successor)))))));
    }

    private static Formula Schedule()
    {
        var k = C("direction", V("H"));
        var stage = All("f", ScalarReply,
            EqOf(C("stage", V("H"), V("f")), C("ite", EqOf(V("H"), D(1)),
                Tuple(C("cast", V("H"), D(0)), Name("nil")),
                Let("u", NumericRun,
                    C("rounds", V("H"), V("f"), C("costBound", V("H")), Constant(Keys, Name("initialAxis"))),
                    Tuple(Seq(Minus, C("cast", V("H"), C("shift", V("H"), First(V("u"))))), Second(V("u")))))));
        var schedule = Let("s", StageType, C("stage", V("H"), C("answer", k)),
            Let("t", StageType, C("stage", V("H"), C("answer", PlusOf(k, D(1)))),
                Tuple(Tuple(First(V("s")), First(V("t"))),
                    C("append", C("map", Lam("x", NatPair, Tuple(k, V("x"))), Second(V("s"))),
                        C("map", Lam("x", NatPair, Tuple(PlusOf(k, D(1)), V("x"))), Second(V("t")))))));
        return All("H", N, And(stage,
            All("answer", Arrow(N, Par(ScalarReply)), EqOf(C("schedule", V("H"), V("answer")), schedule))));
    }

    private static Formula Decode()
    {
        var x = First(V("y"));
        var z = Second(V("y"));
        var rows = Tuple(MinusOf(TimesOf(D(5), x), TimesOf(D(3), z)),
            PlusOf(TimesOf(Seq(Minus, D(3)), x), TimesOf(D(2), z)));
        return All("H", N, All("y", PairType(A, A), EqOf(C("decode", V("H"), V("y")),
            C("apply", C("inverse", Power(C("residueReplace", V("H")), C("direction", V("H")))), rows))));
    }

    private static Formula Effective()
    {
        var h = V("H");
        var v = V("v");
        var k = First(V("t"));
        var c = First(Second(V("t")));
        var g = Second(Second(V("t")));
        var direction = C("direction", h);
        var word = C("compile", h, k, c);
        var entry = C("residueSource", h, v);
        var current = C("residueSource", h, V("current"));
        var entryReply = C("terminalGcd", h, word, v);
        var cut = And(EqOf(current, entry), EqOf(C("terminalGcd", h, word, V("current")), entryReply));
        var triple = And(
            Par(Seq(EqOf(k, direction), Sp, Lor, Sp, EqOf(k, PlusOf(direction, D(1))))),
            LtOf(c, h),
            EqOf(C("count", word, Name("true")), k),
            LeOf(C("count", word, Name("false")), C("graftBound", h)),
            EqOf(g, C("gcd", PlusOf(C("q", C("iterateR", k, v)), c), h)),
            EqOf(g, entryReply),
            All("current", NatPair, Imp(EqOf(current, entry), cut)));
        var result = And(
            EqOf(C("decode", h, First(V("T"))), entry),
            EqOf(First(V("T")), Tuple(
                C("cast", h, C("q", C("iterateR", direction, v))),
                C("cast", h, C("q", C("iterateR", PlusOf(direction, D(1)), v))))),
            EqOf(C("length", Second(V("T"))), C("ite", EqOf(h, D(1)), D(0), TimesOf(D(2), C("costBound", h)))),
            All("t", Triple, Imp(Member(V("t"), Second(V("T"))), triple)));
        return All("H", N, Imp(LeOf(D(1), h), All("v", NatPair,
            Let("T", ScheduleType, C("schedule", h, C("compiledReply", h, v)), result))));
    }

    private static Formula BinaryRounds()
    {
        var successor = Let("c", Binary, C("binaryShift", V("H"), V("b")),
            Let("g", Binary, C("answer", V("c")),
                Let("t", BinaryRun,
                    C("binaryRounds", V("H"), V("answer"), V("j"), C("binaryAdvance", V("H"), V("b"), V("g"))),
                    Tuple(First(V("t")), C("cons", Tuple(V("c"), V("g")), Second(V("t")))))));
        return All("H", N, All("answer", Arrow(Binary, Binary), And(
            All("b", BinaryJoint, EqOf(C("binaryRounds", V("H"), V("answer"), D(0), V("b")), Tuple(V("b"), Name("nil")))),
            All("j", N, All("b", BinaryJoint,
                EqOf(C("binaryRounds", V("H"), V("answer"), PlusOf(V("j"), D(1)), V("b")), successor))))));
    }

    private static Formula BinaryResult()
    {
        var numeric = C("rounds", V("H"), V("answer"), V("j"), V("a"));
        var encoded = C("encodeJoint", V("H"), V("a"));
        var reply = Lam("c", Binary, C("digits", C("answer", C("ofDigits", V("c")))));
        var tape = C("map", Lam("t", NatPair,
            Tuple(C("digits", First(V("t"))), C("digits", Second(V("t"))))), Second(numeric));
        return All("H", N, All("answer", ScalarReply, All("j", N, All("a", Joint, And(
            EqOf(C("binaryRounds", V("H"), reply, V("j"), encoded),
                Tuple(C("encodeJoint", V("H"), First(numeric)), tape)),
            EqOf(C("decodeJoint", V("H"), encoded), V("a")),
            EqOf(C("length", encoded), C("card", C("primeFactors", V("H")))),
            All("n", N, All("d", N,
                Imp(Member(V("d"), C("digits", V("n"))), LtOf(V("d"), D(2))))))))));
    }
}
