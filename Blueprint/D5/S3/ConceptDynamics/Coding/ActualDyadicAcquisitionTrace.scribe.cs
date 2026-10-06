using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ActualDyadicAcquisitionTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual saturated dyadic sensor continuations force chronological midpoint reads and pair-local final queries.",
        H("Actual Continuation Capacity and Saturation"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-continuation-capacity"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace."
                    + "actual_continuation_capacity_and_saturation"),
            H("Capacity saturation excludes early stopping"),
            StatementSource.FromAuthor(CapacityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "In the display, Fin(P), Record, Action(P), Execution(P,b,policy,...) "
                    + "and ForcedReadTrace(P,b,...) are the corresponding Lean types and "
                    + "relations, with implicit P written explicitly and the proof of P>0 "
                    + "suppressed. The constants read and advance are Action constructors. "
                    + "A record is written as <events,reads>; fst and snd are product "
                    + "projections, val is the natural representative of a Fin element, "
                    + "quot is natural-number division, and append and cons are list operations. "
                    + "All subtraction on natural numbers is truncated subtraction.")),
                Paragraph(Text(
                    "Fix a positive block length, a known initial binary high bit, and a "
                    + "deterministic policy on the complete event and raw-read record. The "
                    + "only actions are one forward event, a nondisturbing literal sensor "
                    + "read, and a successful stop. Successful finite executions may stop "
                    + "before making another read; a cutoff is not a successful execution.")),
                Paragraph(Text(
                    "Suppose every source in a finite candidate set has an actual successful "
                    + "continuation from the same complete record, using at most d new reads "
                    + "and returning that source. The candidate set has at most 2^d elements. "
                    + "Its histories and event counts need not range over finite domains.")),
                Paragraph(Text(
                    "Encode each continuation by its raw bits and mathematical zero padding. "
                    + "Two executions with equal codes replay the same deterministic advances, "
                    + "reads and stopping decision. Induction over the actual finite execution "
                    + "therefore gives the same terminal record and output. Exact outputs make "
                    + "the encoding injective; finite function cardinality gives the bound.")),
                Paragraph(Text(
                    "If the candidate set attains 2^d elements, the finite encoding is onto. "
                    + "An alleged shorter successful continuation can be extended by a code "
                    + "whose first padded position is one. Its actual realization shares the "
                    + "old raw prefix and must stop with the same word, contradicting zero "
                    + "padding. Every such continuation using at most d new reads has exactly d reads.")),
                Paragraph(Text(
                    "This capacity bound does not assert dyadic interval rigidity, a final "
                    + "query phase, a causal noisy-phase decoder, or repair label thresholds."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actual-next-read-decomposition"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace."
                    + "actual_next_read_decomposition"),
            H("Silent forward evolution reaches a common next-read event"),
            StatementSource.FromAuthor(NextReadFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix one complete record and one successful actual execution with at "
                    + "least one new read. There is a finite event count N at least as large "
                    + "as the current count. The policy advances at every intervening event "
                    + "with the old read record and chooses a read at N.")),
                Paragraph(Text(
                    "Every other successful execution with a new read from the same complete "
                    + "record reaches that same N. Its first bit is the literal sensor at N, "
                    + "and its tail is an actual execution from the record with that bit "
                    + "appended. The proof extracts the finite silent segment from the first "
                    + "execution and uses the conflicting advance and read choices to exclude "
                    + "different first-read events.")),
                Paragraph(Text(
                    "Nonempty actual words are a hypothesis here; capacity saturation "
                    + "supplies them for a positive full read budget. This result does not "
                    + "assume that an arbitrary cutoff or empty execution has a last read."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actual-dyadic-interval-trace"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace."
                    + "actual_dyadic_interval_trace"),
            H("Actual dyadic continuations force the chronological midpoint trace"),
            StatementSource.FromAuthor(IntervalTraceFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a common complete record and the original source interval "
                    + "[a,a+2^d), contained in a positive block. Every source in that "
                    + "interval has an actual identifying continuation with at most d "
                    + "new physical reads. For each such actual continuation, its final "
                    + "read record is the old record followed by a forced chronological trace.")),
                Paragraph(Text(
                    "At a node with d+1 remaining reads, extract the common next actual "
                    + "query N. The literal raw sensor partitions the interval at "
                    + "theta=P-(N mod P). Its two actual children have at most 2^d "
                    + "sources by remaining-read capacity. Natural interval cardinality "
                    + "therefore forces theta=a+2^d. Both children admit actual successful "
                    + "continuations from their corresponding appended raw records.")),
                Paragraph(Text(
                    "Induction on the remaining budget applies the same construction in "
                    + "the child selected by the acquired threshold bit. Every recorded "
                    + "query has the forced midpoint phase and its raw value is "
                    + "(b+floor(N/P)+e) mod 2. The full event quotient preserves arbitrary "
                    + "whole-period waits. Query counts remain nondecreasing in the model.")),
                Paragraph(Text(
                    "The trace contains actual read event counts; subsequent silent "
                    + "reporting advances do not change it. The common pair-local "
                    + "final query is established by the following actual two-run theorem."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actual-pair-common-final-query"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace."
                    + "actual_pair_common_final_query"),
            H("The actual source pair shares its pre-final record and last query"),
            StatementSource.FromAuthor(PairQueryFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Consider two actual executions from the same complete record, with "
                    + "source representatives having the same quotient by two. Both sources "
                    + "are in one dyadic interval with even lower endpoint, have the saturated "
                    + "positive read count, and have the forced chronological traces supplied "
                    + "by the interval theorem. The traces agree before their last entries, "
                    + "whose literal event count N is also common.")),
                Paragraph(Text(
                    "At every earlier midpoint, its even threshold puts the paired sources "
                    + "on the same side. Their raw bits therefore agree. The common-next-read "
                    + "decomposition moves both actual continuations to the same appended "
                    + "complete record. Induction reaches the final two-source interval, where "
                    + "the next physical query is the last read for both executions.")),
                Paragraph(Text(
                    "For t=floor(r/2), the actual event obeys N mod P=P-1-2t. The two "
                    + "literal final bits are (b+floor(N/P)+(r mod 2)) mod 2 and the analogous "
                    + "expression for the other source. The policy chooses read on the common "
                    + "pre-final record. From each appended final-bit record an actual execution "
                    + "with no further reads reaches its original terminal record.")),
                Paragraph(Text(
                    "The event quotient retains every whole-period wait, and the common N "
                    + "is local to the source pair. These operational results do not supply a "
                    + "chronological prefix writer, an all-error noisy-phase decoder, or the "
                    + "TM8.1 label and supplementary-bit thresholds."))),
            DescribeRole.Theorem))));

    private static Formula CapacityFormula()
    {
        var budget = V("remaining");
        var record = V("record");
        var candidates = V("candidates");
        var capacity = new Formula.Power(D(2), budget);
        var success = All(Then(Rel(V("x"), FormulaRelationOperator.MemberOf, candidates),
            Some(Both(Run(V("x"), record, V("w"), V("T")), AtMost(Len(V("w")), budget),
                EqualTo(Call("snd", V("T")), V("x"))), ("w", Bits()), ("T", Terminal()))), ("x", FinP()));
        var full = All(Then(Both(Rel(V("r"), FormulaRelationOperator.MemberOf, candidates),
            Run(V("r"), record, V("word"), V("terminal")), AtMost(Len(V("word")), budget)),
            EqualTo(Len(V("word")), budget)),
            ("r", FinP()), ("word", Bits()), ("terminal", Terminal()));
        return Disp(All(Then(Both(Below(D(0), V("P")), success),
            Both(AtMost(Call("card", candidates), capacity), Then(EqualTo(Call("card", candidates), capacity), full))),
            ("P", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P")))),
            ("record", C("Record")), ("remaining", NatType()), ("candidates", Call("Finset", FinP()))));
    }

    private static Formula NextReadFormula()
    {
        var record = V("record");
        var n = V("N");
        var reads = Call("reads", record);
        var other = All(Then(Both(Run(V("s"), record, V("otherword"), V("otherterminal")),
            UnequalTo(V("otherword"), Nil())), Some(Both(
                EqualTo(V("otherword"), Call("cons", Sensor(V("s"), n), V("tail"))),
                Run(V("s"), Rec(n, Append(reads, Singleton(Pair(n, Sensor(V("s"), n))))),
                    V("tail"), V("otherterminal"))), ("tail", Bits()))),
            ("s", FinP()), ("otherword", Bits()), ("otherterminal", Terminal()));
        return Disp(All(Then(Both(Below(D(0), V("P")),
            Run(V("r"), record, V("word"), V("terminal")), UnequalTo(V("word"), Nil())),
            Some(Both(AtMost(Call("events", record), n), EqualTo(App(V("policy"), Rec(n, reads)), C("read")),
                All(Then(Both(AtMost(Call("events", record), V("k")), Below(V("k"), n)),
                    EqualTo(App(V("policy"), Rec(V("k"), reads)), C("advance"))), ("k", NatType())), other),
                ("N", NatType()))),
            ("P", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P")))),
            ("record", C("Record")), ("r", FinP()), ("word", Bits()), ("terminal", Terminal())));
    }

    private static Formula IntervalTraceFormula()
    {
        var lo = V("lo");
        var d = V("d");
        var end = PlusOf(lo, new Formula.Power(D(2), d));
        var record = V("record");
        var success = All(Then(Both(AtMost(lo, Val(V("x"))), Below(Val(V("x")), end)),
            Some(Both(Run(V("x"), record, V("w"), V("T")), AtMost(Len(V("w")), d),
                EqualTo(Call("snd", V("T")), V("x"))), ("w", Bits()), ("T", Terminal()))), ("x", FinP()));
        return Disp(All(Then(Both(Below(D(0), V("P")), AtMost(end, V("P")), success,
            AtMost(lo, Val(V("r"))), Below(Val(V("r")), end),
            Run(V("r"), record, V("word"), V("terminal")), AtMost(Len(V("word")), d)),
            Some(Both(EqualTo(Reads(V("terminal")), Append(Call("reads", record), V("trace"))),
                Forced(V("r"), lo, d, V("trace"))), ("trace", Past()))),
            ("P", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P")))),
            ("record", C("Record")), ("lo", NatType()), ("d", NatType()),
            ("r", FinP()), ("word", Bits()), ("terminal", Terminal())));
    }

    private static Formula PairQueryFormula()
    {
        var record = V("record");
        var lo = V("lo");
        var depth = PlusOf(V("d"), D(1));
        var end = PlusOf(lo, new Formula.Power(D(2), depth));
        var n = V("N");
        var past = V("past");
        var old = Append(Call("reads", record), past);
        return Disp(All(Then(Both(Below(D(0), V("P")), Call("Even", lo), AtMost(end, V("P")),
            EqualTo(Prefix(V("r")), Prefix(V("s"))),
            AtMost(lo, Val(V("r"))), Below(Val(V("r")), end), AtMost(lo, Val(V("s"))), Below(Val(V("s")), end),
            Run(V("r"), record, V("word"), V("terminal")), Run(V("s"), record, V("otherword"), V("otherterminal")),
            EqualTo(Len(V("word")), depth), EqualTo(Len(V("otherword")), depth),
            EqualTo(Reads(V("terminal")), Append(Call("reads", record), V("trace"))),
            EqualTo(Reads(V("otherterminal")), Append(Call("reads", record), V("othertrace"))),
            Forced(V("r"), lo, depth, V("trace")), Forced(V("s"), lo, depth, V("othertrace"))),
            Some(Both(EqualTo(V("trace"), Append(past, Singleton(Pair(n, V("bit"))))),
                EqualTo(V("othertrace"), Append(past, Singleton(Pair(n, V("otherbit"))))),
                PhaseEquation(n, V("r")), BitEquation(V("bit"), n, V("r")), BitEquation(V("otherbit"), n, V("s")),
                EqualTo(App(V("policy"), Rec(n, old)), C("read")),
                Run(V("r"), Rec(n, Append(old, Singleton(Pair(n, V("bit"))))), Nil(), V("terminal")),
                Run(V("s"), Rec(n, Append(old, Singleton(Pair(n, V("otherbit"))))), Nil(), V("otherterminal"))),
                ("past", Past()), ("N", NatType()), ("bit", Call("Fin", D(2))), ("otherbit", Call("Fin", D(2))))),
            ("P", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P")))),
            ("record", C("Record")), ("lo", NatType()), ("d", NatType()), ("r", FinP()), ("s", FinP()),
            ("word", Bits()), ("otherword", Bits()), ("terminal", Terminal()), ("otherterminal", Terminal()),
            ("trace", Past()), ("othertrace", Past())));
    }

    private static FormulaIdentifier Variable(string name) => FormulaIdentifier.Create(name switch
    {
        "policy" => "p",
        "record" => "R",
        "remaining" => "m",
        "candidates" => "C",
        "word" => "w",
        "terminal" => "T",
        "otherword" => "v",
        "otherterminal" => "U",
        "lo" => "a",
        "trace" => "A",
        "othertrace" => "B",
        "past" => "H",
        "bit" => "y",
        "otherbit" => "Y",
        "history" => "h",
        "query" => "n",
        "epsilon" => "e",
        "writer" => "f",
        "decoder" => "D",
        "tail" => "t",
        _ => name,
    });
    private static Formula V(string name) => new Formula.Symbol(Variable(name));
    private static Formula C(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(Variable(v.Name), v.Type))], body);
    private static Formula Some(Formula body, params (string Name, Formula Type)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. variables.Select(v => new Formula.BoundVariable(Variable(v.Name), v.Type))], body);
    private static Formula Both(params Formula[] clauses) => clauses.Length == 1 ? clauses[0] :
        new Formula.Logic(clauses[0], FormulaLogicOperator.And, Both(clauses[1..]));
    private static Formula Then(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula EqualTo(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula UnequalTo(Formula left, Formula right) => Rel(left, FormulaRelationOperator.NotEqual, right);
    private static Formula AtMost(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Below(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula PlusOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula MinusOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula TimesOf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) => Seq(Open, left, Sp, Times, Sp, right, Close);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula Rec(Formula events, Formula reads) => Seq(Langle, Sp, events, Comma, Sp, reads, Rangle);
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula Singleton(Formula element) => Seq(OpenBracket, element, CloseBracket);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinP() => Call("Fin", V("P"));
    private static Formula Bits() => Call("List", Call("Fin", D(2)));
    private static Formula Past() => Call("List", Product(NatType(), Call("Fin", D(2))));
    private static Formula Terminal() => Product(C("Record"), FinP());
    private static Formula Val(Formula r) => Call("val", r);
    private static Formula Prefix(Formula r) => Call("quot", Val(r), D(2));
    private static Formula Len(Formula word) => Call("length", word);
    private static Formula Reads(Formula terminal) => Call("reads", Call("fst", terminal));
    private static Formula Append(Formula left, Formula right) => Call("append", left, right);
    private static Formula Sensor(Formula r, Formula n) => Call("rawSensor", V("P"), V("b"), r, n);
    private static Formula Run(Formula r, Formula record, Formula word, Formula terminal) =>
        Call("Execution", V("P"), V("b"), V("policy"), r, record, word, terminal);
    private static Formula Forced(Formula r, Formula lo, Formula d, Formula trace) =>
        Call("ForcedReadTrace", V("P"), V("b"), r, lo, d, trace);
    private static Formula PhaseEquation(Formula n, Formula r) => EqualTo(new Formula.Modulo(n, V("P")),
        MinusOf(MinusOf(V("P"), D(1)), TimesOf(D(2), Prefix(r))));
    private static Formula BitEquation(Formula bit, Formula n, Formula r) => EqualTo(Val(bit),
        new Formula.Modulo(PlusOf(PlusOf(Val(V("b")), Call("quot", n, V("P"))),
            new Formula.Modulo(Val(r), D(2))), D(2)));

}
