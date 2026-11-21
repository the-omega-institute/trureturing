using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class RussoExtremalHeapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/RussoExtremalHeap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The extremal Heap sweep ends in reversal for sizes two modulo four.",
        H("Russo’s extremal Heap sweep"),
        Blocks(
            Paragraph(Text("A state sends each item to its position. An array sends each position to its item, so the emitted arrays are the inverses of the states. Position zero is position one of the paper. Products act from right to left.")),
            Node("topParkingItem", "Items prescribed at the highest level", NatCarrier(
                All("j", Nat, Equal(B("topParkingItem", N, J), App(Pow(B("literalZ", N), Add(J, Num(1))), Top(N))))),
                "Definition 22 reads the successive positive powers of the quotient at the last position. The zero power gives the item already parked there."),
            Node("extremalTopPartner", "The physical top-level partner", NatCarrier(
                All("j", Nat, Equal(B("extremalTopPartner", N, J),
                    B("parkingPartner", B("actualU", N), Top(N), B("topParkingItem", N), J)))),
                "Theorem 18(a) recovers the physical partner from the prescribed item by advancing the current state through the lower call."),
            Node("extremalSweep", "The ordered physical sweep", NatCarrier(
                Both(
                    F.Seq(Equal(N, Num(2)), F.Longrightarrow,
                        Equal(B("extremalSweep", N), B("cyclicSweep", N, Num(1)))),
                    F.Seq(NotEqual(N, Num(2)), F.Longrightarrow, F.Sp, Equal(B("extremalSweep", N),
                        Ordered(B("penultimateSweep", N), Top(N), B("extremalTopPartner", N), Subtract(N, Num(1))))))),
                "Definition 22 uses the cyclic or classic call at size two. At larger admissible sizes the penultimate calls occur in the order fixed by the computed top partners."),
            Node("sweepArrays", "The ordered emitted arrays", Carrier(
                All("swaps", SwapList(A), All("start", Perm(A),
                    Equal(B("sweepArrays", V("swaps"), V("start")),
                        Method("map", B("sweepStates", V("swaps"), V("start")),
                            Lambda("state", Inverse(V("state")))))))),
                "Section 3.1 emits the starting state followed by the state immediately after each physical swap. Inversion reads each state as an array."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact enumeration and reversal in the residue-two class"),
                StatementSource.FromAuthor(F.Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Section 10 item 1 asks for the case n congruent to two modulo four. At n = 2 the cyclic call swaps zero and one. For n at least six the quotient is formed using the actual net of the penultimate sweep. Its entire orbit gives the prescribed order, and every recorded partner lies below the last position.")),
                    Paragraph(Text("The first return to the support of the penultimate net is the square of its even cycle after a transposition of consecutive support coordinates. This joins the two alternating cycles. An excursion has length one or two, and every point outside the support is the intermediate point of a two-step return. The full-carrier orbit follows from the project’s first-visit theorem.")),
                    Paragraph(Text("The parked item distinguishes the recursive blocks. Each block runs through its own fiber in lower-call order. The stored swap connects the last array of the preceding block and the first array of the next block. The net is the lower net to the nth power followed, in composition order, by the quotient. Reversal is maximal because, at the first unequal position, the larger candidate entries already occur in the shared prefix.")),
                    Paragraph(Text("Brackets on a list in an optional lookup return some entry when the index is in range and none otherwise. Index zero and the index one less than the length give the displayed head and last queries on these nonempty lists. The step formula includes the optional lookup on the swap list at every natural index."))),
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula Result()
    {
        var swaps = V("swaps");
        var emitted = V("emitted");
        var array = V("array");
        var pair = V("ab");
        var state = V("last");
        var previous = V("previous");
        var lower = V("lower");
        var tau = F.Tau;
        var round = I;

        Formula Arrays(Formula schedule, Formula start) => B("sweepArrays", schedule, start);
        Formula Step() => All("i", Nat, Equal(Index(emitted, Add(I, Num(1))),
            Method("bind", Index(emitted, I), Lambda("array",
                Method("map", Index(swaps, I), Lambda("ab", Multiply(array, PairSwap(pair))))))));
        Formula Edge() => Lambda("p", Lambda("q", Some("a", Fin(N), Some("b", Fin(N),
            Both(NotEqual(V("a"), V("b")), Equal(V("q"), Multiply(V("p"), Swap(V("a"), V("b")))))))));
        Formula Chain() => Method("IsChain", emitted, Edge());
        Formula TopOrder() => Q("Function", "Bijective",
            Lambda("j", Fin(N), App(Pow(B("literalZ", N), Val(J)), Top(N))));
        Formula Block(Formula rounds) => Ordered(lower, Top(N), B("extremalTopPartner", N), rounds);

        var boundary = All("i", Nat, If(Lt(I, Subtract(N, Num(1))), new Formula.Aligned([
            Let(lower, B("penultimateSweep", N)),
            Let(previous, Block(round)),
            Let(state, B("executeSwaps", previous, Num(1))),
            Let(tau, Swap(B("extremalTopPartner", N, round), Top(N))),
            Equal(Arrays(Block(Add(round, Num(1))), Num(1)),
                Append(Arrays(previous, Num(1)), Arrays(lower, Multiply(tau, state)))),
            Equal(Last(Arrays(previous, Num(1))), B("some", Inverse(state))),
            Equal(Index(Arrays(lower, Multiply(tau, state)), Num(0)),
                B("some", Multiply(Inverse(state), tau))),
        ])));
        var net = Multiply(Pow(B("actualU", N), N), B("literalZ", N));
        var large = If(Le(Num(6), N), new Formula.Aligned([
            Method("IsCycleOn", B("literalZ", N), Q("Set", "univ")),
            TopOrder(),
            All("j", Nat, If(Lt(J, Subtract(N, Num(1))),
                Lt(Val(B("extremalTopPartner", N, J)), Subtract(N, Num(1))))),
            Equal(B("executeSwaps", swaps, Num(1)), net),
            Equal(net, Reversal),
            boundary,
        ]));
        return new Formula.Aligned([
            Equal(B("extremalSweep", Num(2)), Brackets(Pair(Num(0), Num(1)))),
            Equal(Arrays(B("extremalSweep", Num(2)), Num(1)), Brackets(Num(1), Reversal)),
            All("n", Nat, If(Both(Le(Num(2), N), Equal(Mod(N, Num(4)), Num(2))), new Formula.Aligned([
                Let(swaps, B("extremalSweep", N)),
                Let(emitted, Arrays(swaps, Num(1))),
                Equal(Index(emitted, Num(0)), B("some", Num(1))),
                Method("Nodup", emitted),
                All("array", Perm(Fin(N)), Mem(array, emitted)),
                Equal(Length(emitted), Method("factorial", N)),
                Chain(),
                Step(),
                Equal(Last(emitted), B("some", Reversal)),
                Equal(Inverse(B("executeSwaps", swaps, Num(1))), Reversal),
                All("array", Perm(Fin(N)), F.Seq(Equal(array, Reversal), F.Lor,
                    Q("Pi", "Lex", Par(F.Lt), Par(F.Lt),
                        Lambda("i", App(array, I)), Lambda("i", Q("Fin", "rev", I))))),
                All("ab", Product(Fin(N), Fin(N)), If(Mem(pair, swaps), NotEqual(Fst(pair), Snd(pair)))),
                large,
            ]))),
        ]);
    }

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/russo2026extremalheap");
    private static Formula A => F.Alpha;
    private static Formula I => V("i");
    private static Formula J => V("j");
    private static Formula N => V("n");
    private static Formula Nat => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Reversal => Name("Fin", "revPerm");
    private static Formula V(string name) => Id(name);
    private static Formula B(string name, params Formula[] args) => Call(name, args);
    private static Formula Name(string owner, string name) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(owner), F.Dot, F.Id(name)));
    private static Formula Q(string owner, string name, params Formula[] args) => App(Name(owner, name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Brackets(Formula first) => F.Seq(F.OpenBracket, first, F.CloseBracket);
    private static Formula Brackets(Formula first, Formula second) =>
        F.Seq(F.OpenBracket, first, F.Comma, second, F.CloseBracket);
    private static Formula Fin(Formula size) => B("Fin", size);
    private static Formula Perm(Formula type) => Q("Equiv", "Perm", type);
    private static Formula Product(Formula x, Formula y) => F.Seq(x, F.Times, y);
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
    private static Formula Inverse(Formula x) => Pow(Par(x), F.Seq(F.Minus, F.D(1)));
    private static Formula Mod(Formula x, Formula y) =>
        F.Seq(x, F.Sp, F.Operatorname, F.Grp(F.Id("mod")), F.Sp, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mem(Formula x, Formula xs) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, xs);
    private static Formula Both(Formula x, Formula y) => F.Seq(Par(x), F.Land, F.Sp, Par(y));
    private static Formula If(Formula given, Formula body) => F.Seq(Par(given), F.Longrightarrow, F.Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Binder(F.Forall, V(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => Binder(F.Exists, V(name), type, body);
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
    private static Formula Top(Formula size) => B("slot", size, Subtract(size, Num(1)));
    private static Formula Ordered(Formula lower, Formula top, Formula partners, Formula rounds) =>
        B("orderedSweep", lower, top, partners, rounds);
    private static Formula Let(Formula x, Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("let")), F.Sp, x, F.Colon, F.Eq, value);
    private static Formula Append(Formula xs, Formula ys) => F.Seq(xs, F.Plus, F.Plus, ys);
    private static Formula Index(Formula xs, Formula i) => F.Seq(xs, Brackets(i));
    private static Formula Length(Formula xs) => Method("length", xs);
    private static Formula Last(Formula xs) => Index(xs, Subtract(Length(xs), Num(1)));
}
