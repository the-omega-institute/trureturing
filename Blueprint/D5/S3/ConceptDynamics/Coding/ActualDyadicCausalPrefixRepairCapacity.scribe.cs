using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ActualDyadicCausalPrefixRepairCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual acquired prefixes support causal fixed labels and uniform closed-error recovery.",
        H("Actual Causal Prefix Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-acquired-prefix-and-final-query"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity."
                    + "actual_acquired_prefix_and_final_query"),
            H("Successful actual schedules acquire the prefix before the final query"),
            StatementSource.FromAuthor(AcquiredPrefixFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The display uses the corresponding Lean types and relations, writing "
                    + "implicit P explicitly and suppressing its positivity proof: Execution, "
                    + "ReachedRecord, acquiredPrefix, rawSensor, terminalPhase, "
                    + "prefixCircularDistance, OperationalRepairFeasible and "
                    + "operationalLabelMinimum. A record is <events,reads>; read is the "
                    + "Action.read constructor. The operators fst, snd, val, length, append "
                    + "and quot are product projections, the Fin representative, list length, "
                    + "list append and natural division; real is coercion to the reals. "
                    + "Natural subtraction is truncated. IsLeast and dist have their Lean "
                    + "meanings; the set builder binds its own K.")),
                Paragraph(Text(
                    "Fix P=2^(d+1), the known initial bit and one deterministic policy. "
                    + "Every source has a finite successful actual execution identifying "
                    + "it using at most d+1 new reads. Every such execution has exactly "
                    + "d+1 reads. Sources with the same quotient by two have a common "
                    + "pre-final history of d reads and a common literal final query N.")),
                Paragraph(Text(
                    "The pre-final history is reached by the primitive forward and read "
                    + "actions. Each acquired raw bit is normalized modulo two using "
                    + "the known initial bit and its recorded event quotient. Starting "
                    + "at v=0, the chronological update v=2v+e returns floor(r/2) on "
                    + "that history, before the last raw bit or any clock noise exists. "
                    + "Thus any chosen mathematical prefix label factors through this record.")),
                Paragraph(Text(
                    "Capacity and interval inputs are derived from all-source success. "
                    + "The forced midpoint trace is derived for each actual execution. "
                    + "Induction over that trace proves the chronological fold law. "
                    + "A separate physical execution split locates the record preceding "
                    + "the last read. Silent reporting advances preserve the read list.")),
                Paragraph(Text(
                    "N mod P=P-1-2 floor(r/2), and the final raw bit is "
                    + "(b+floor(N/P)+(r mod 2)) mod 2. Whole-period waits are retained "
                    + "in the quotient. Common N is asserted only within a source pair. "
                    + "This statement does not establish noisy circle geometry, a "
                    + "uniform all-error decoder, or the complete label minima."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actual-causal-closed-error-recovery"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity."
                    + "actual_causal_closed_error_recovery"),
            H("Actual causal labels separate closed phase overlaps exactly"),
            StatementSource.FromAuthor(ClosedRecoveryFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All-source finite successful executions supply a history and literal "
                    + "last query for each source. Every actual bounded successful execution "
                    + "has that final read record. The chronological normalized prefix is "
                    + "floor(r/2). History equality holds exactly within each source pair, "
                    + "and its last query is common within that pair.")),
                Paragraph(Text(
                    "The real-circle distance between actual final phases equals twice "
                    + "the integer circular distance between prefixes. The proof handles "
                    + "both the direct arc and the arc crossing the seam, including equality "
                    + "and antipodal points. Two closed phase balls overlap exactly when "
                    + "the center distance is at most twice the nonnegative error bound. "
                    + "The overlap witness is a midpoint in a real lift, then quotiented.")),
                Paragraph(Text(
                    "One prefix label is realized by a writer on the reached pre-final "
                    + "record. It precedes the final bit and every clock error. A single "
                    + "receiver works for all actual sources and all admissible errors "
                    + "exactly when equal labels never occur on overlapping distinct "
                    + "prefixes. Necessity selects two actual source bits yielding Y=0 "
                    + "and one shared admissible phase; these are two source realizations.")),
                Paragraph(Text(
                    "For sufficiency, the mathematical receiver selects a prefix using "
                    + "the phase and label alone. The fixed known policy determines its "
                    + "event quotient. Subtracting b and that quotient from Y in ZMod 2 "
                    + "recovers the last source bit. The arbitrary default is used only "
                    + "outside the admissible actual image. Retaining the full prefix "
                    + "proves feasibility and existence of the least operational alphabet, "
                    + "defined by receiver feasibility. This is an existence result for "
                    + "fixed known b and policy; no executable replay or running-time "
                    + "bound is asserted.")),
                Paragraph(Text(
                    "The result does not give the complete numerical label regimes or "
                    + "their supplementary-bit costs. Alphabet compression measures "
                    + "supplementary terminal information; it does not measure all memory "
                    + "used by the acquisition controller or the known policy."))),
            DescribeRole.Theorem))));

    private static Formula AcquiredPrefixFormula()
    {
        var depth = PlusOf(V("d"), D(1));
        var n = V("N");
        var past = V("past");
        var initial = Rec(D(0), Nil());
        return Disp(All(Then(Both(Below(D(0), V("P")), EqualTo(V("P"), new Formula.Power(D(2), depth)),
            Success(initial, depth), EqualTo(Prefix(V("r")), Prefix(V("s"))),
            Run(V("r"), initial, V("word"), V("terminal")), Run(V("s"), initial, V("otherword"), V("otherterminal")),
            AtMost(Len(V("word")), depth), AtMost(Len(V("otherword")), depth)),
            Some(Both(EqualTo(Len(V("word")), depth), EqualTo(Len(V("otherword")), depth), EqualTo(Len(past), V("d")),
                EqualTo(Call("acquiredPrefix", V("P"), V("b"), past, D(0)), Prefix(V("r"))),
                EqualTo(Reads(V("terminal")), Append(past, Singleton(Pair(n, V("bit"))))),
                EqualTo(Reads(V("otherterminal")), Append(past, Singleton(Pair(n, V("otherbit"))))),
                Reached(V("r"), Rec(n, past)), Reached(V("s"), Rec(n, past)),
                PhaseEquation(n, V("r")), BitEquation(V("bit"), n, V("r")), BitEquation(V("otherbit"), n, V("s")),
                EqualTo(App(V("policy"), Rec(n, past)), C("read")),
                Run(V("r"), Rec(n, Append(past, Singleton(Pair(n, V("bit"))))), Nil(), V("terminal")),
                Run(V("s"), Rec(n, Append(past, Singleton(Pair(n, V("otherbit"))))), Nil(), V("otherterminal"))),
                ("past", Past()), ("N", NatType()), ("bit", Call("Fin", D(2))), ("otherbit", Call("Fin", D(2))))),
            ("P", NatType()), ("d", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P")))),
            ("r", FinP()), ("s", FinP()), ("word", Bits()), ("otherword", Bits()),
            ("terminal", Terminal()), ("otherterminal", Terminal())));
    }

    private static Formula ClosedRecoveryFormula()
    {
        var depth = PlusOf(V("d"), D(1));
        var initial = Rec(D(0), Nil());
        var r = V("r");
        var s = V("s");
        var history = App(V("history"), r);
        var query = App(V("query"), r);
        var reads = Append(history, Singleton(Pair(query, Sensor(r, query))));
        var actual = All(Some(Both(Run(r, initial, V("word"), V("terminal")),
            EqualTo(Len(V("word")), depth), EqualTo(Call("snd", V("terminal")), r), EqualTo(Len(history), V("d")),
            EqualTo(Call("acquiredPrefix", V("P"), V("b"), history, D(0)), Prefix(r)),
            Reached(r, Rec(query, history)), EqualTo(Reads(V("terminal")), reads), PhaseEquation(query, r)),
            ("word", Bits()), ("terminal", Terminal())), ("r", FinP()));
        var invariant = All(Then(EqualTo(Prefix(r), Prefix(s)), Both(EqualTo(history, App(V("history"), s)),
            EqualTo(query, App(V("query"), s)))), ("r", FinP()), ("s", FinP()));
        var historyIff = All(IffOf(EqualTo(history, App(V("history"), s)), EqualTo(Prefix(r), Prefix(s))),
            ("r", FinP()), ("s", FinP()));
        var geometry = All(EqualTo(Distance(Phase(r), Phase(s)),
            TimesOf(D(2), Call("real", Call("prefixCircularDistance", V("P"), r, s)))), ("r", FinP()), ("s", FinP()));
        var everyRun = All(Then(Both(Run(r, initial, V("word"), V("terminal")), AtMost(Len(V("word")), depth)),
            EqualTo(Reads(V("terminal")), reads)), ("r", FinP()), ("word", Bits()), ("terminal", Terminal()));
        var circle = Call("AddCircle", Call("real", V("P")));
        var decoderType = Arrow(circle, Arrow(Call("Fin", D(2)), Arrow(Call("Fin", V("K")), FinP())));
        var decodes = Some(All(Then(AtMost(Distance(V("q"), Phase(r)), V("epsilon")),
            EqualTo(App(V("decoder"), V("q"), Sensor(r, query), App(V("z"), Prefix(r))), r)),
            ("r", FinP()), ("q", circle)), ("decoder", decoderType));
        var separates = All(Then(Both(UnequalTo(Prefix(r), Prefix(s)),
            AtMost(Distance(Phase(r), Phase(s)), TimesOf(D(2), V("epsilon")))),
            UnequalTo(App(V("z"), Prefix(r)), App(V("z"), Prefix(s)))), ("r", FinP()), ("s", FinP()));
        var causal = All(Some(Both(All(EqualTo(App(V("writer"), Rec(query, history)), App(V("z"), Prefix(r))),
            ("r", FinP())), IffOf(decodes, separates)), ("writer", Arrow(C("Record"), Call("Fin", V("K"))))),
            ("K", NatType()), ("z", Arrow(NatType(), Call("Fin", V("K")))));
        var feasible = Call("OperationalRepairFeasible", V("P"), V("b"), V("query"), V("epsilon"), V("K"));
        var feasibleSet = Seq(OpenBrace, V("K"), Colon, Sp, NatType(), Sp, Mid, Sp, feasible, CloseBrace);
        var least = Call("IsLeast", feasibleSet,
            Call("operationalLabelMinimum", V("P"), V("b"), V("query"), V("epsilon")));
        var errors = All(Then(AtMost(D(0), V("epsilon")), Both(least, causal)),
            ("epsilon", Seq(Mathbb, Grp(F.Id("R")))));
        return Disp(All(Then(Both(Below(D(0), V("P")), EqualTo(V("P"), new Formula.Power(D(2), depth)),
            Success(initial, depth)), Some(Both(actual, invariant, historyIff, geometry, everyRun, errors),
                ("history", Arrow(FinP(), Past())), ("query", Arrow(FinP(), NatType())))),
            ("P", NatType()), ("d", NatType()), ("b", Call("Fin", D(2))), ("policy", Arrow(C("Record"), Call("Action", V("P"))))));
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
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
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
    private static Formula Reached(Formula r, Formula record) =>
        Call("ReachedRecord", V("P"), V("b"), V("policy"), r, Rec(D(0), Nil()), record);
    private static Formula Phase(Formula r) => Call("terminalPhase", V("P"), r);
    private static Formula Distance(Formula left, Formula right) => Call("dist", left, right);
    private static Formula PhaseEquation(Formula n, Formula r) => EqualTo(new Formula.Modulo(n, V("P")),
        MinusOf(MinusOf(V("P"), D(1)), TimesOf(D(2), Prefix(r))));
    private static Formula BitEquation(Formula bit, Formula n, Formula r) => EqualTo(Val(bit),
        new Formula.Modulo(PlusOf(PlusOf(Val(V("b")), Call("quot", n, V("P"))),
            new Formula.Modulo(Val(r), D(2))), D(2)));
    private static Formula Success(Formula record, Formula budget) =>
        All(Some(Both(Run(V("x"), record, V("w"), V("T")),
            AtMost(Len(V("w")), budget), EqualTo(Call("snd", V("T")), V("x"))),
            ("w", Bits()), ("T", Terminal())), ("x", FinP()));
}
