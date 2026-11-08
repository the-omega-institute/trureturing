using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class Machine3626Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Computability/BinaryMachine/Machine3626.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Computability/bala2026machine3626");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed Moebius and totient divisor sum counts every transition of the one-sided machine on every positive binary input.",
        H("Exact transition count of machine 3626"),
        Blocks(
            Paragraph(Text("The external question is Peter Bala's conjecture in OEIS A393210, also recorded in A069517; the alias pair is one question. Its unchanged prospective registration is https://github.com/the-omega-institute/trureturing/issues/25808#issuecomment-6587694551. The scope is every positive natural input, with no finite cutoff, tape bound or counter width.")),
            Node("State", "Two machine states", null, DescribeRole.Definition,
                "State has exactly the constructors A and B; termination is a boundary crossing, rather than a third state."),
            Node("Cfg", "Unbounded half-tape configuration", null, DescribeRole.Definition,
                "Cfg contains state : State, left : List Bool, and right : List Bool. The head scans the first left bit. Absent left bits are implicit blank zero. The right list records cells between the head and the fixed right boundary. Both list lengths are unbounded."),
            Node("exitRight", "Right move and boundary crossing", null, DescribeRole.Definition,
                "For writtenLeft : List Bool and right : List Bool, exitRight writtenLeft [] is none. For right = b :: rest it is some (Cfg.mk State.B (b :: writtenLeft) rest). This consumes the nearest right cell and enters B after writing; none denotes the actual boundary crossing."),
            Node("step", "Literal transition semantics", null, DescribeRole.Definition,
                "Cfg has a state A or B and two unbounded Boolean lists. The left list begins at the scanned cell and continues toward the most significant end; absent cells are implicit blank zero. The right list records the finite distance to the fixed right boundary. The four simultaneous read/write/state/move rules are A0 to A0L, A1 to B1R, B0 to A1L, and B1 to B0R. exitRight returns none precisely when a right move crosses the boundary; otherwise its result has state B. There is no separate halt state."),
            Node("Trace", "Counted first boundary crossing", null, DescribeRole.Definition,
                "Trace.zero counts zero transitions at a configuration. Trace.cons adds one nonhalting transition to a trace from its successor. Trace.crossing counts exactly one transition whose result is none. No constructor continues a trace after none, so Trace t c none records the first boundary crossing at transition t, rather than merely a visit to a terminal state."),
            Node("initial", "Positive binary input at the right edge", All("n", NatType(),
                EqTo(Call("initial", V("n")), App(Q("Cfg", "mk"), Q("State", "A"),
                    App(Q("Nat", "bits"), V("n")), EmptyList()))), DescribeRole.Definition,
                "Nat.bits is least-significant-bit first. The head scans that bit in state A at the right boundary; the empty right list fixes the actual boundary. Blank cells extend infinitely to the left of the most significant digit. The final result excludes n = 0."),
            Node("block", "Zeros before the first one", All("k", NatType(), All("higher", ListBool(),
                EqTo(Call("block", V("k"), V("higher")),
                    App(Q("List", "append"), App(Q("List", "replicate"), V("k"), V("false")),
                        App(Q("List", "cons"), V("true"), V("higher")))))), DescribeRole.Definition,
                "The block contains k zero bits followed by its first one and arbitrary higher bits. The lists have no fixed maximum length."),
            Node("block_first_crossing", "A restoring block crosses in the exact count", BlockFormula(), DescribeRole.Theorem,
                "The recursive trace restores the lower block after each of two smaller traversals and then exits. Its transition count satisfies T(0) = 1 and T(k+1) = 2 T(k) + 3. Solving this recurrence gives 4 times 2 to the k minus 3. Higher cells remain arbitrary. The last crossing transition is included."),
            Node("positive_input_first_crossing", "Every positive input has the required operational trace", PrefixFormula(), DescribeRole.Theorem,
                "Binary recursion finds the first one of every positive input. The restoring-block trace then supplies the actual first boundary crossing. This operational theorem is a live prerequisite of the exact arithmetic result."),
            Node("result", "Exact signed Moebius and totient formula", ResultFormula(), DescribeRole.Theorem,
                "The source sentence is: Conjecture: a(n) = Sum_{d | n} m(d)^2 * phi(d), where m(n) = Sum_{d | n} (-1)^(d+1) * moebius(d) = A069517(n) and phi(n) denotes Euler's totient function A000010(n). Cf. A296306. This is the conjecture line in OEIS A393210, revision 18. For every natural n greater than zero there exists a transition count t with Trace t (initial n) none and the displayed integer equality. Both divisor sums range over all positive divisors; powers of minus one, Moebius values, the square and the outer sum are interpreted in the integers. The totient and the natural transition count are cast to integers. The proof uses the published arithmetic multiplicativity and prime-power values through pinned Mathlib's Moebius and totient results. Odd prime factors contribute one to the outer divisor transform; the 2-power factor contributes 4 times 2 to the k minus 3, matching the same binary prefix used by the operational trace. This is a symbolic theorem for all positive inputs. It makes no claim for input zero or for another machine or boundary convention."))));

    private static DocumentBlock Node(string name, string title, Formula? formula, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("machine3626-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role,
            openProblemResolutionClaim: name == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala-machine3626-exact-halting-time"), ResolutionKind.Proved)
                : null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula IntType() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula ListBool() => Call("List", V("Bool"));
    private static Formula EmptyList() => Q("List", "nil");
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string n, Formula type, Formula body) => Seq(Exists, Sp, V(n), Colon, Sp, type, Comma, Sp, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Time(Formula k) => Sub(Mul(D(4), Pow(D(2), k)), D(3));
    private static Formula TraceAt(Formula time, Formula cfg) => Call("Trace", time, cfg, V("none"));
    private static Formula Positive(Formula n) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
    private static Formula Cast(Formula n) => Parenthesized(Seq(n, Colon, Sp, IntType()));
    private static Formula DivSum(string variable, Formula n, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(V(variable), Sp, InMacro, Sp, App(Q("Nat", "divisors"), n))), Sp, body);
    private static Formula BlockFormula() => All("k", NatType(), All("higher", ListBool(),
        TraceAt(Time(V("k")), App(Q("Cfg", "mk"), Q("State", "A"),
            Call("block", V("k"), V("higher")), EmptyList()))));
    private static Formula PrefixFormula() => All("n", NatType(), ImpliesTo(Positive(V("n")),
        Some("k", NatType(), Some("higher", ListBool(), And(
            EqTo(App(Q("Nat", "bits"), V("n")), Call("block", V("k"), V("higher"))),
            TraceAt(Time(V("k")), Call("initial", V("n"))))))));
    private static Formula ResultFormula()
    {
        var inner = DivSum("e", V("d"), Mul(Pow(Parenthesized(Sub(D(0), D(1))), Add(V("e"), D(1))),
            App(Q("ArithmeticFunction", "moebius"), V("e"))));
        var total = DivSum("d", V("n"), Mul(Pow(Parenthesized(inner), D(2)),
            Cast(App(Q("Nat", "totient"), V("d")))));
        return All("n", NatType(), ImpliesTo(Positive(V("n")), Some("t", NatType(),
            And(TraceAt(V("t"), Call("initial", V("n"))), EqTo(Cast(V("t")), total)))));
    }
}
