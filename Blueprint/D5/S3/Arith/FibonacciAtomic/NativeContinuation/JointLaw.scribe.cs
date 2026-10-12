using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.NativeContinuation;

internal sealed class JointLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] clauses) => Seq([.. clauses.SelectMany(
        (c, i) => i == 0 ? new Formula[] { Par(c) } : [Sp, Land, Sp, Par(c)])]);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Words => Call("List", V("Window"));
    private static Formula Source(Formula n) => Call("Source", n);
    private static Formula WindowTuple(Formula n) => Seq(Call("Fin", n), Sp, To, Sp, V("Window"));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula P(Formula sign) => Call("law", V("n"), V("t"), sign);
    private static Formula SignedZero => Seq(
        Pow(Par(Seq(Minus, D(1))), V("n")), Sp, V("t"), Sp,
        Slash, Sp, Pow(D(2), Par(Seq(V("n"), Minus, D(1)))));

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-joint-law-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula formula, params string[] prose) =>
        Describe.Lean(DescribeId.Create("native-joint-law-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks([.. prose.Select(p => Paragraph(Text(p)))]),
            DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same full-support natural window laws preserve every proper seam-coordinate joint table while their actual appended-null reply laws remain separated.",
        H("Full-Support Native Window Laws and Actual Null Continuation"),
        Blocks(
            Paragraph(Text("Window is the original five-letter alphabet, in the order null, low, high, ends, middle. Its natural displacements are respectively (0,0), (1,0), (1,1), (2,1), (0,1). The original high-to-low reader uses S(a,b)=(a+2b,2a+3b), q(a,b)=2a+3b, and the guard excluding an incoming true seam followed by a true high bit. The initial seam is false and the initial composition is (0,0).")),
            Definition("composition", "Natural chronological composition",
                "composition(w), also denoted C(w), folds the original update C'=S(C)+bitComposition(b) along the window list. The coordinates are natural numbers. Every prefix uses the same word and update."),
            Definition("digits", "The same padded binary word",
                "digits(w) maps the complete existing highBits(w) from Bool to Fin 2, with false mapped to zero and true mapped to one. It reverses each printed three-bit window and preserves the chronological window order, the leading null windows and all original positions."),
            Theorem("actual_state", "The original reader's complete successful state",
                All("w", Words, Imp(Call("legal", V("false"), Call("highBits", V("w"))),
                    EqOf(Call("eval", Call("rawMachine", D(0)), V("w")),
                        Call("some", Pair(Call("finalSeam", V("w")),
                            Call("residue", D(0), Call("C", V("w")))))))),
                "eval is the existing reader's initialized DFA evaluation. finalSeam(w) is false for the empty word and the low bit of its last window otherwise. residue(0,C(w)) casts the two natural coordinates to the integer carrier. The natural history determines both the chronological fold and its terminal seam. Applying this equality to each legal prefix realizes the complete reported seam history in the same reader."),
            Theorem("actual_quantity", "Actual natural execution",
                All("w", Words, Imp(Call("legal", V("false"), Call("highBits", V("w"))),
                    EqOf(Call("task", D(0), V("w")), Call("some", Call("q", Call("C", V("w"))))))),
                "task(0,w) is the existing integer output, not a reduced modular output. The natural quantity in the displayed formula is cast to the integer carrier ZMod 0. A legal source has the natural composition determined by its actual history. The natural-history realization identifies the existing reader's successful state; folding that same history determines its final composition."),
            Theorem("composition_coordinates", "Exact Fibonacci coordinates of the source",
                All("w", Words, EqOf(Call("fibPair", Call("digits", V("w"))), Call("S", Call("C", V("w"))))),
                "fibPair is the existing padded Fibonacci two-register evaluator. Appending each original window advances the registers three times and adds precisely S(bitComposition(b)). Induction over the chronological word therefore gives the formula for every finite word. This arithmetic formula alone does not make an illegal word a successful source."),
            Definition("Source", "The entire legal fixed-length source",
                "Source(n) consists of all functions from Fin n to Window whose complete high-to-low bits are legal from the false seam. There is no final-seam restriction, End action, leading-nonzero test or independence premise. List.ofFn gives the original window list. Its actual seam vector consists of the initial false seam followed by the low bit of every window."),
            Definition("reply", "The actual natural null reply",
                "reply(w)=qS(C(List.ofFn(w))) is a natural number. The appended input is the existing null window. It is legal at either live seam, applies the full clock, and sets the next seam to false."),
            Theorem("actual_null_reply", "Realization of the specified continuation",
                All("n", Natural, All("w", Source(V("n")), EqOf(
                    Call("task", D(0), Call("appendNull", Call("ofFn", V("w")))),
                    Call("some", Call("reply", V("w")))))),
                "appendNull(v) denotes v followed by the singleton null window. The displayed natural reply is cast to the same integer output carrier as task(0). The equality ranges over the entire legal source, including the all-null source and sources ending at seam one."),
            Theorem("native_reply_injective", "Exact separation at fixed length",
                All("n", Natural, All("u", Source(V("n")), All("v", Source(V("n")),
                    Imp(EqOf(Call("reply", V("u")), Call("reply", V("v"))),
                        EqOf(V("u"), V("v")))))),
                "The actual null reply is injective on Source(n). Appending the null window and one zero digit makes the first Fibonacci register equal to that reply. The existing equal-width canonical numeric-order theorem identifies its strict order with the padded words' lexicographic order. Equal replies therefore have equal padded bit words, and each original three-bit window recovers its own letter. This is a fixed-length assertion; different amounts of leading padding are not identified with the same source."),
            Definition("bitWindow", "The null and middle letters",
                "bitWindow sends zero to null and one to middle. Both letters have false high and low bits."),
            Definition("embed", "The actual zero-seam cube",
                "embed(n,b) applies bitWindow at each original position. Every resulting source is legal, the map is injective, and its complete seam vector is the all-false vector of length n+1."),
            Definition("cubeLaw", "The existing real parity laws",
                "cubeLaw(n,e) is the real cast of the existing rational fair parityLaw(n,e). A zero coordinate has sign minus one and a one coordinate sign plus one. For positive n and e equal to minus one or one, the mass is one and all proper coordinate restrictions have equal complete tables under the two signs."),
            Definition("law", "A common positive background on the entire source",
                "law(n,t,e)(w)=(1-t)/card(Source(n))+t*pushforward(embed(n),cubeLaw(n,e))(w). Here pushforward is the existing CapacityMonotone finite-source real pushforward: pushforward(f,p)(y) sums p(x) over the source points with f(x)=y. Its output carrier need not be finite, and signed real tables are allowed. Thus both laws use the uniform background on the entire legal five-mode source, not merely the embedded cube. The parameter t is real."),
            Definition("seams", "The full seam history",
                "seams(w) is false followed by the low bit of every source window, in its original order. It includes the initial and final seams."),
            Definition("mass", "The mass of a finite source event",
                "mass(p,E) sums p(w) over all finite source points satisfying the predicate E. The same mass definition underlies the joint, seam and conditional tables."),
            Definition("jointMass", "Separate full joint reports for proper coordinate sets",
                "jointMass(p,A,s,y) sums p(w) over sources with seams(w)=s and w(i)=y(i) for every i in A. The sets A retain the original positions. Empty, noncontiguous and n-1 element sets are included. Although y is written as a full tuple, only its restriction to A is tested. These are separate probability tables, not a paired archive combining all reports from the same sample."),
            Definition("seamEventMass", "Events of the complete seam history",
                "seamEventMass(p,E) is the total p-mass of sources whose full seam vector lies in E."),
            Definition("conditionalMass", "Positive-event conditional coordinate tables",
                "conditionalMass(p,E,A,y) divides the mass of E together with the coordinate restriction by seamEventMass(p,E). Conditional-law assertions concern positive denominators; no conditional law is asserted at a zero-mass event."),
            Definition("linearReadout", "Fixed linear readouts of actual prefix compositions",
                "linearReadout(j,a,b,w)=a*C(take(j,List.ofFn(w))).first+b*C(take(j,List.ofFn(w))).second, with the natural coordinates cast to the reals. The coefficients are fixed; they do not depend on the source or its replies."),
            Definition("sourceTV", "Total variation of finite source laws",
                "sourceTV(p,q) is half the sum over the entire Source(n) of the absolute value of p(w)-q(w)."),
            Definition("replyTV", "Total variation of the complete actual reply laws",
                "replyTV(p,q) is half the sum of the absolute reply-mass difference over the actual finite image of reply on Source(n). The masses are pushforward(reply,p) and pushforward(reply,q). Values outside this image have zero mass under both laws."),
            Theorem("native_probability_separation", "All proper joint reports and actual continuation separation",
                ProbabilityFormula(),
                "The two laws in the formula are law(n,t,1) and law(n,t,-1). Total(p) denotes the finite sum of all source masses. J abbreviates jointMass, M abbreviates seamEventMass, and K abbreviates conditionalMass. Expected(p,H) is the finite sum of p(w)*H(w). The sign set contains minus one and one; A ranges over Finset(Fin n), s over finite Bool lists, y over full Window tuples, and E over all predicates on the complete seam history.",
                "Both laws are strictly positive on every legal word and have total mass one. The embedded cube has one constant actual seam vector, so its joint report tests only the selected binary coordinates. The existing parity marginal equality then gives every proper table, including the empty table. The common uniform background preserves these equalities. Summing over any seam event gives equal event masses; division by a common positive mass gives the conditional tables.",
                "The actual null zero fiber is precisely the all-null source. Its cube sign is minus one to the power n, so the signed zero-event difference is the displayed nonzero quantity. Prefix induction expresses every fixed linear composition readout using the individual window marginals, hence their expectations agree, including the actual null quantity.",
                "The two cube parity laws have disjoint support, each of total mass one. Their signed difference scales by t after the common background is added, giving source total variation t. The actual natural null reply is injective at fixed length, so its pushforward preserves this complete total variation. The entire-law separation is independent of n at fixed t, although the single zero-event difference decreases with n.",
                "These assertions establish the finite probability and actual null-continuation relations. They assert no indicator L2 realization, local Gram spectrum, all-position Fibonacci marginal formula, recovery from paired archives, infinite-source compatibility or finite-sample decision theorem."))));

    private static Formula ProbabilityFormula()
    {
        var n = V("n"); var t = V("t"); var w = V("w");
        var plus = P(D(1)); var minus = P(Seq(Minus, D(1)));
        var a = V("A"); var s = V("s"); var y = V("y"); var e = V("E");
        var proper = Seq(a, Sp, Neq, Sp, V("univ"));
        var coordinateSet = Call("Finset", Call("Fin", n));
        var signs = Seq(V("e"), Sp, InMacro, Sp,
            OpenBrace, Minus, D(1), Comma, D(1), CloseBrace);
        var probability = All("e", Integer, Imp(signs, And(
            All("w", Source(n), LtOf(D(0), Call("law", n, t, V("e"), w))),
            EqOf(Call("Total", P(V("e"))), D(1)))));
        var joint = All("A", coordinateSet, Imp(proper,
            All("s", Call("List", V("Bool")), All("y", WindowTuple(n),
                EqOf(Call("J", plus, a, s, y), Call("J", minus, a, s, y))))));
        var eventType = Seq(Call("List", V("Bool")), Sp, To, Sp, V("Prop"));
        var events = All("E", eventType, And(
            EqOf(Call("M", plus, e), Call("M", minus, e)),
            Imp(LtOf(D(0), Call("M", plus, e)), All("A", coordinateSet,
                Imp(proper, All("y", WindowTuple(n),
                    EqOf(Call("K", plus, e, a, y), Call("K", minus, e, a, y))))))));
        var actual = All("w", Source(n), EqOf(
            Call("task", D(0), Call("appendNull", Call("ofFn", w))),
            Call("some", Call("reply", w))));
        var zero = And(EqOf(Seq(Call("pushforward", V("reply"), plus, D(0)), Sp, Minus, Sp,
            Call("pushforward", V("reply"), minus, D(0))), SignedZero), Seq(SignedZero, Sp, Neq, Sp, D(0)));
        var linear = All("j", Natural, Imp(LeOf(V("j"), n), All("a", Real, All("b", Real,
            EqOf(Call("Expected", plus, Call("linearReadout", V("j"), V("a"), V("b"))),
                Call("Expected", minus, Call("linearReadout", V("j"), V("a"), V("b"))))))));
        return All("n", Natural, Imp(LeOf(D(3), n), All("t", Real,
            Imp(And(LtOf(D(0), t), LtOf(t, D(1))), And(probability, joint, events, actual, zero, linear,
                EqOf(Call("Expected", plus, V("reply")), Call("Expected", minus, V("reply"))),
                EqOf(Call("sourceTV", plus, minus), t), EqOf(Call("replyTV", plus, minus), t))))));
    }
}
