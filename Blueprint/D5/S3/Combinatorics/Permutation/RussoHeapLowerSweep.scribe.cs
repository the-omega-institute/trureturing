using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class RussoHeapLowerSweepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered lower sweeps and their penultimate net.",
        H("Parking orders and lower Heap sweeps"),
        Blocks(
            Node("parkingPartner", "Recovering a physical swap partner", ParkingPartner(),
                "Theorem 18(a) uses the block start followed by the lower net. In the formula θ is the sequence of block starts. The current item e(j) is prescribed by the parking order.", literature: true),
            Node("path", "The initial segment of the parking order", ForType(
                All("top", A, All("e", Arrow(Nat, A), All("j", Nat, Equal(B("path", TopPosition, E, J),
                    Cons(TopPosition, Q("List", "ofFn", Lambda("i", Fin(J), App(E, Val(I)))))))))),
                "The first entry is the initially parked item. Each later entry is a prescribed item."),
            Node("parked", "The item at each block start", ForType(
                All("top", A, All("e", Arrow(Nat, A), All("j", Nat, Rows(
                    Equal(B("parked", TopPosition, E, Num(0)), TopPosition),
                    Equal(B("parked", TopPosition, E, Add(J, Num(1))), App(E, J))))))),
                "Index zero is the start before the first scheduled swap."),
            Node("slot", "Zero-based positions", NatCarrier(All("i", Nat,
                Equal(B("slot", N, I), Q("Fin", "ofNat", N, I)))),
                "Indices are interpreted using the residue modulo the size of the carrier."),
            Node("slot_val", "The value of an in-range position", NatCarrier(All("i", Nat,
                If(Lt(I, N), Equal(Val(B("slot", N, I)), I)))),
                "An index below the carrier size represents itself.", theorem: true),
            Node("initial", "The first positions in order", NatCarrier(All("k", Nat,
                Equal(B("initial", N, K), Q("List", "ofFn", Lambda("i", Fin(K), B("slot", N, Val(I))))))),
                "The order is increasing in the zero-based indices."),
            Node("initial_nodup", "A prefix of positions has no repetition", NatCarrier(All("k", Nat,
                If(Le(K, N), Method("Nodup", B("initial", N, K))))),
                "Each in-range index identifies a different finite position.", theorem: true),
            Node("cyclicPartner", "Cyclic schedule partners", CyclicPartner(),
                "Definition 3 uses the even or odd level rule. The physical top index k is one less than the level, and round index zero corresponds to the first swap.", literature: true),
            Node("penultimateItem", "The prescribed penultimate parking order", NatCarrier(
                All("j", Nat, Rows(Let(M, Divide(Subtract(N, Num(2)), Num(2))),
                    If(Lt(J, M), Equal(B("penultimateItem", N, J), B("slot", N, J))),
                    If(Le(M, J), Equal(B("penultimateItem", N, J),
                        B("slot", N, Subtract(Subtract(Multiply(Num(3), M), Num(1)), J))))))),
                "Definition 22 lists 1 through m first and then 2m through m+1 in decreasing order. The list items and round indices here are zero-based.", literature: true),
            Node("orderedSweep", "The ordered list of physical swaps", ForType(
                All("lower", SwapList(A), All("top", A, All("s", Arrow(Nat, A), All("j", Nat, Rows(
                    Equal(Ordered(Lower, TopPosition, S, Num(0)), Lower),
                    Equal(Ordered(Lower, TopPosition, S, Add(J, Num(1))),
                        Append(Ordered(Lower, TopPosition, S, J), Cons(Pair(App(S, J), TopPosition), Lower))))))))),
                "Section 3.1 calls the lower sweep first. Each round then performs its swap and starts the next lower call.", literature: true),
            Node("executeSwaps", "Executing the ordered swaps", SwapTraversal("executeSwaps", "foldl"),
                "The state sends each item to its position, so a transposition of positions multiplies it on the left."),
            Node("cyclicSweep", "The recursive cyclic sweep", NatCarrier(All("k", Nat, Rows(
                Equal(B("cyclicSweep", N, Num(0)), Brackets()),
                Equal(B("cyclicSweep", N, Add(K, Num(1))),
                    Ordered(B("cyclicSweep", N, K), B("slot", N, Add(K, Num(1))),
                        B("cyclicPartner", N, Add(K, Num(1))), Add(K, Num(1))))))),
                "Level one has no physical swap. At higher levels the chosen partners are those of Definition 3.", literature: true),
            Node("executeParkingSweep", "Net formula for a parking sweep", ParkingNet(),
                "Theorem 18(a)–(b) follows by conjugating the physical swap back to the prescribed items in each round, then collecting the transpositions in order.", theorem: true),
            Node("penultimateSweep", "The penultimate sweep of Definition 22", NatCarrier(Rows(
                Let(Lower, B("cyclicSweep", N, Subtract(N, Num(3)))),
                Let(TopPosition, B("slot", N, Subtract(N, Num(2)))),
                Equal(B("penultimateSweep", N), Ordered(Lower, TopPosition,
                    B("parkingPartner", B("executeSwaps", Lower, Num(1)), TopPosition, B("penultimateItem", N)),
                    Subtract(N, Num(2)))))),
                "The ambient carrier keeps the largest position available as a fixed point. The lower call is the cyclic sweep on the first n−2 positions.", literature: true),
            Node("actualU", "The net of the penultimate sweep", NatCarrier(
                Equal(B("actualU", N), B("executeSwaps", B("penultimateSweep", N), Num(1)))),
                "This net executes the penultimate sweep from the identity in the same carrier."),
            Node("literalZ", "The quotient that prescribes the top order", NatCarrier(
                Equal(B("literalZ", N), Multiply(Pow(B("actualU", N), F.Seq(F.Minus, Par(F.Seq(N, F.Colon, Integer)))), Reversal))),
                "Definition 22 places the target reversal on the right of the negative power of the actual penultimate net.", literature: true),
            Node("formPerm_ofFn_pow", "Powers of the cycle of a list", CyclePower(),
                "A cycle advances by p indices modulo its length along the list of distinct labels.", theorem: true),
            Node("nodup_ofFn_labels", "Distinct indices give distinct labels", ForType(
                All("label", Arrow(Nat, A), All("L", Nat, If(LabelsInjective(),
                    Method("Nodup", Labels()))))),
                "The hypothesis compares labels only at in-range indices.", theorem: true),
            Node("uArrow", "The coordinate formula for the penultimate net", NetCoordinate(),
                "The coordinate formula for the moving points uses m, half the size of the cyclic lower call."),
            Node("literal_net_value", "The actual net satisfies the coordinate formula",
                All("m", Nat, If(Le(Num(2), M), All("x", Fin(Add(Multiply(Num(2), M), Num(2))),
                    Equal(Val(B("actualU", Add(Multiply(Num(2), M), Num(2)), X)), B("uArrow", M, Val(X)))))),
                "The cyclic lower net and the prescribed parking cycle compose to give the displayed value. The range includes every position of the ambient carrier.", theorem: true),
            Node("sweepStates", "The ordered sequence of visited states", SwapTraversal("sweepStates", "scanl"),
                "Section 3.1 emits an initial state and then one new state after each physical swap.", literature: true),
            Node("sweepStates_ordered_succ", "Appending the next block of emissions", OrderedStates(),
                "The next lower call begins with the state obtained by swapping the scheduled positions in the preceding terminal state.", theorem: true),
            Node("FixesOutside", "Fixed positions outside a prefix",
                All("n", Nat, All("k", Nat, All("p", Perm(Fin(N)), Equal(B("FixesOutside", K, P),
                    Par(All("x", Fin(N), If(Le(K, Val(X)), Equal(App(P, X), X)))))))),
                "This predicate fixes the full complement of the initial prefix."),
            Node("PrefixSweep", "Complete enumeration of a prefix", PrefixSweepFormula(),
                "The unvisited positions are fixed in every emitted state. The actual swaps always exchange two distinct positions within the prefix."),
            Node("prefixNet_fixes", "The net fixes unvisited positions",
                All("n", Nat, All("k", Nat, All("lower", SwapList(Fin(N)), If(B("PrefixSweep", K, Lower),
                    B("FixesOutside", K, B("executeSwaps", Lower, Num(1))))))),
                "The net is the last state in the visited list.", theorem: true),
            Node("extendParkingSweep", "Extending by the final position", ExtendParking(),
                "Distinct parked items yield disjoint fibers indexed by the preimage of the final position. The lower sweep enumerates each fiber in call order. This extension assumes the new position is the final one of the ambient carrier.", theorem: true),
            Node("cyclic_prefixSweep", "Cyclic calls enumerate the moving prefix", NatCarrier(
                All("k", Nat, If(Lt(K, N), B("PrefixSweep", Add(K, Num(1)), B("cyclicSweep", N, K))))),
                "Induction on the level applies the parked-item decomposition and checks the distinct item order for both level parities.", theorem: true),
            Node("penultimate_prefixSweep", "The prescribed penultimate call is complete", NatCarrier(
                If(Both(Le(Num(6), N), Equal(Mod(N, Num(4)), Num(2))),
                    B("PrefixSweep", Subtract(N, Num(1)), B("penultimateSweep", N)))),
                "The two pieces of the prescribed parking order are disjoint and exhaust the moving items below the penultimate position.", theorem: true)
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string detail,
        bool theorem = false, bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(detail))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula ParkingPartner()
    {
        var theta = F.Theta;
        var state = App(theta, J);
        var next = App(C, App(state, App(E, J)));
        return Carrier(All("C", Perm(A), All("top", A, All("e", Arrow(Nat, A),
            F.Seq(F.Exists, F.Sp, theta, F.Colon, Arrow(Nat, Perm(A)), F.Comma, Rows(
                Equal(App(theta, Num(0)), Num(1)),
                All("j", Nat, Equal(App(theta, Add(J, Num(1))), Multiply(Multiply(Swap(next, TopPosition), C), state))),
                All("j", Nat, Equal(B("parkingPartner", C, TopPosition, E, J), next))))))));
    }

    private static Formula CyclicPartner()
    {
        var even = Equal(Mod(K, Num(2)), Num(0));
        var odd = NotEqual(Mod(K, Num(2)), Num(0));
        var first = Equal(J, Num(0));
        var later = NotEqual(J, Num(0));
        var last = Equal(Add(J, Num(1)), K);
        var beforeLast = NotEqual(Add(J, Num(1)), K);
        Formula Value(Formula value) => Equal(B("cyclicPartner", N, K, J), B("slot", N, value));
        return NatCarrier(All("k", Nat, All("j", Nat, Rows(
            If(even, Value(Num(0))),
            If(Both(odd, first), Value(Subtract(K, Num(1)))),
            If(Both(Both(odd, later), last), Value(Num(0))),
            If(Both(Both(odd, later), beforeLast), Value(J))))));
    }

    private static Formula ParkingNet() => Carrier(
        All("lower", SwapList(A), All("top", A, All("e", Arrow(Nat, A),
            Rows(Let(C, B("executeSwaps", Lower, Num(1))),
                If(Equal(App(C, TopPosition), TopPosition),
                    All("j", Nat, Equal(B("executeSwaps",
                        Ordered(Lower, TopPosition, B("parkingPartner", C, TopPosition, E), J), Num(1)),
                        Multiply(Pow(C, Add(J, Num(1))), Method("formPerm", B("path", TopPosition, E, J)))))))))));

    private static Formula Labels() => Q("List", "ofFn",
        Lambda("i", Fin(V("L")), App(V("label"), Val(I))));

    private static Formula LabelsInjective() =>
        All("i", Nat, If(Lt(I, V("L")), All("j", Nat, If(Lt(J, V("L")),
            If(Equal(App(V("label"), I), App(V("label"), J)), Equal(I, J))))));

    private static Formula CyclePower() => Carrier(
        All("label", Arrow(Nat, A), All("L", Nat, If(Method("Nodup", Labels()),
            All("p", Nat, All("i", Nat, If(Lt(I, V("L")),
                Equal(App(Pow(Method("formPerm", Labels()), P), App(V("label"), I)),
                    App(V("label"), Mod(Add(I, P), V("L")))))))))));

    private static Formula NetCoordinate()
    {
        var twoM = Multiply(Num(2), M);
        var successor = Add(X, Num(1));
        var other = NotEqual(X, twoM);
        Formula Readout(Formula value) => Equal(B("uArrow", M, X), value);
        return All("m", Nat, All("x", Nat, Rows(
            If(Equal(X, twoM), Readout(Num(1))),
            If(Both(other, Lt(successor, M)), Readout(Add(X, Num(2)))),
            If(Both(other, Equal(successor, M)), Readout(Num(0))),
            If(Both(Both(other, Lt(M, successor)), Equal(X, M)), Readout(twoM)),
            If(Both(Both(other, Lt(M, successor)), NotEqual(X, M)), Readout(X)))));
    }

    private static Formula SwapTraversal(string declaration, string traversal) => Carrier(
        All("swaps", SwapList(A), All("start", Perm(A),
            Equal(B(declaration, Swaps, Start), Q("List", traversal,
                Lambda("state", Lambda("ab", Multiply(PairSwap(AB), V("state")))), Start, Swaps)))));

    private static Formula OrderedStates()
    {
        var previous = V("previous");
        return Carrier(All("lower", SwapList(A), All("top", A, All("s", Arrow(Nat, A),
            All("j", Nat, All("start", Perm(A), Rows(
                Let(previous, Ordered(Lower, TopPosition, S, J)),
                Equal(B("sweepStates", Ordered(Lower, TopPosition, S, Add(J, Num(1))), Start),
                    Append(B("sweepStates", previous, Start), B("sweepStates", Lower,
                        Multiply(Swap(App(S, J), TopPosition), B("executeSwaps", previous, Start))))))))))));
    }

    private static Formula PrefixSweepFormula() => All("n", Nat, All("k", Nat,
        All("swaps", SwapList(Fin(N)), Rows(
            Let(V("states"), B("sweepStates", Swaps, Num(1))),
            F.Seq(B("PrefixSweep", K, Swaps), F.Leftrightarrow, F.Sp, Par(Both(
                Method("Nodup", V("states")), Both(
                    All("p", Perm(Fin(N)), F.Seq(Mem(P, V("states")), F.Leftrightarrow, F.Sp, B("FixesOutside", K, P))),
                    All("ab", Product(Fin(N), Fin(N)), If(Mem(AB, Swaps),
                        Both(Lt(Val(Fst(AB)), K), Both(Lt(Val(Snd(AB)), K), NotEqual(Fst(AB), Snd(AB))))))))))))));

    private static Formula ExtendParking()
    {
        var next = Add(K, Num(1));
        var top = B("slot", N, K);
        var distinct = All("i", Nat, If(Le(I, K), All("j", Nat, If(Le(J, K),
            If(Equal(B("parked", top, E, I), B("parked", top, E, J)), Equal(I, J))))));
        return NatCarrier(All("k", Nat, All("lower", SwapList(Fin(N)), All("e", Arrow(Nat, Fin(N)),
            If(Both(Equal(next, N), Both(B("PrefixSweep", K, Lower), distinct)),
                Rows(Let(S, B("parkingPartner", B("executeSwaps", Lower, Num(1)), top, E)),
                    B("PrefixSweep", next, Ordered(Lower, top, S, K)),
                    All("j", Nat, If(Lt(J, K), Lt(Val(App(S, J)), K)))))))));
    }

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/russo2026extremalheap");
    private static Formula A => F.Alpha;
    private static Formula AB => V("ab");
    private static Formula C => V("C");
    private static Formula E => V("e");
    private static Formula I => V("i");
    private static Formula J => V("j");
    private static Formula K => V("k");
    private static Formula M => V("m");
    private static Formula N => V("n");
    private static Formula P => V("p");
    private static Formula S => V("s");
    private static Formula X => V("x");
    private static Formula Lower => V("lower");
    private static Formula Start => V("start");
    private static Formula Swaps => V("swaps");
    private static Formula TopPosition => V("top");
    private static Formula Nat => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Integer => F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
    private static Formula Reversal => Name("Fin", "revPerm");
    private static Formula V(string name) => Id(name);
    private static Formula B(string name, params Formula[] args) => Call(name, args);
    private static Formula Name(string owner, string name) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(owner), F.Dot, F.Id(name)));
    private static Formula Q(string owner, string name, params Formula[] args) => App(Name(owner, name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Brackets() => F.Seq(F.OpenBracket, F.CloseBracket);
    private static Formula Brackets(Formula first) => F.Seq(F.OpenBracket, first, F.CloseBracket);
    private static Formula Fin(Formula size) => B("Fin", size);
    private static Formula Perm(Formula type) => Q("Equiv", "Perm", type);
    private static Formula Product(Formula x, Formula y) => F.Seq(x, F.Times, y);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula SwapList(Formula type) => B("List", Product(type, type));
    private static Formula Pair(Formula x, Formula y) => Par(F.Seq(x, F.Comma, y));
    private static Formula Swap(Formula x, Formula y) => Q("Equiv", "swap", x, y);
    private static Formula PairSwap(Formula pair) => Swap(Fst(pair), Snd(pair));
    private static Formula Fst(Formula pair) => F.Seq(pair, F.Dot, F.D(1));
    private static Formula Snd(Formula pair) => F.Seq(pair, F.Dot, F.D(2));
    private static Formula Val(Formula value) => Method("val", value);
    private static Formula Method(string name, Formula source, params Formula[] args) =>
        args.Length == 0 ? F.Seq(Par(source), F.Dot, F.Id(name)) :
            App(F.Seq(Par(source), F.Dot, F.Id(name)), args);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mod(Formula x, Formula y) =>
        F.Seq(x, F.Sp, F.Operatorname, F.Grp(F.Id("mod")), F.Sp, y);
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mem(Formula x, Formula xs) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, xs);
    private static Formula Both(Formula x, Formula y) => F.Seq(Par(x), F.Land, F.Sp, Par(y));
    private static Formula If(Formula given, Formula body) => F.Seq(Par(given), F.Longrightarrow, F.Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Binder(F.Forall, V(name), type, body);
    private static Formula Binder(Formula quantifier, Formula variable, Formula type, Formula body) =>
        F.Seq(quantifier, Par(F.Seq(variable, F.Colon, type)), F.Comma, body);
    private static Formula ForType(Formula body) => Binder(F.Forall, A, F.Id("Type"), body);
    private static Formula Carrier(Formula body) =>
        ForType(F.Seq(Brackets(B("DecidableEq", A)), F.Comma, body));
    private static Formula NatCarrier(Formula body) =>
        All("n", Nat, F.Seq(Brackets(B("NeZero", N)), F.Comma, body));
    private static Formula Lambda(string name, Formula body) => F.Seq(V(name), F.Mapsto, F.Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        F.Seq(Par(F.Seq(V(name), F.Colon, type)), F.Mapsto, F.Sp, body);
    private static Formula Ordered(Formula lower, Formula top, Formula partners, Formula rounds) =>
        B("orderedSweep", lower, top, partners, rounds);
    private static Formula Rows(params Formula[] rows) => new Formula.Aligned([.. rows]);
    private static Formula Let(Formula x, Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("let")), F.Sp, x, F.Colon, F.Eq, value);
    private static Formula Cons(Formula x, Formula xs) => F.Seq(x, F.Colon, F.Colon, xs);
    private static Formula Append(Formula xs, Formula ys) => F.Seq(xs, F.Plus, F.Plus, ys);
}
