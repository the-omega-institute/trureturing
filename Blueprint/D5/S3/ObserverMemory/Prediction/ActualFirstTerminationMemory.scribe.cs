using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ActualFirstTerminationMemoryDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed universal code has exact first-termination pulses, attained per-program memory minima, and no computable uniform bound.",
        H("Actual First-Termination Memory"),
        Blocks(
            new DocumentBlock.Section(H("The fixed program and its operational clock"), Blocks(
                Paragraph(Text(
                    "The source uses one fixed code u and places the natural number e in the literal "
                        + "input [e] at index e+1. The code is the standard Nat.Partrec numbering transported through "
                        + "decodeCode and encodeCode; no family of codes is selected as e varies. The "
                        + "finite-data machine has Data = List Nat, a typed continuation Stack, and "
                        + "Cfg = Data + (Stack x Data). The normal and returning interpreters implement "
                        + "the pinned ToPartrec operational clauses.")),
                Paragraph(Text(
                    "step is exactly one effective ToPartrec.step: a terminal Data configuration maps "
                        + "to none, while a live continuation performs one returning transition. The "
                        + "initial clock is 0 -> halt [] and e+1 -> normal u [] [e], hence "
                        + "encode(c)+1 -> normal u [] [encode(c)] for c : Nat.Partrec.Code. run u e n "
                        + "is the n-fold Option transition from that initial state. pulse u e t is true "
                        + "exactly when run u e t = some q for a present terminal configuration q whose "
                        + "next native step returns Option.none. A transition entering Cfg.halt still "
                        + "returns Option.some; the pulse occurs at the terminal configuration itself. "
                        + "Thus the clock counts native transitions. At index 0 the initial configuration "
                        + "is already halt [], so t=0 is an actual first-termination case.")),
                Paragraph(Text(
                    "step_decode and run_decode identify this clock pointwise and at every index with "
                        + "the effective ToPartrec.step. first_terminal adds the exact first-terminal "
                        + "equivalence: the terminal state occurs at t and every earlier pulse is false.")))),
            new DocumentBlock.Section(H("Single-pulse minima and the two uniform obstructions"), Blocks(
                Paragraph(Text(
                    "For a Boolean stream b, unarySizes b is the set of finite state-carrier cardinalities "
                        + "realized by one start state, one update, and one Boolean readout. A unique hit at "
                        + "t is therefore the delayed pulse decide(n = t). The imported delayed-pulse "
                        + "minimum, transported by single_start_dp_sizes, gives IsLeast(unarySizes b, t+2) "
                        + "at a hit; the all-false stream has the attained one-state minimum. Consequently "
                        + "every operational program has an attained finite minimum, including the t=0 case.")),
                Paragraph(Text(
                    "MinimumStateBound b s means that s e bounds every attained minimum for b e. "
                        + "ExhaustiveZeroPrefix b N is the inclusive cutoff property: if all n <= N e are "
                        + "false, then every n is false. prefixHit computes the finite prefix witness using "
                        + "length N(e)+1, so an effective bound or inclusive cutoff would decide the "
                        + "undecidable existential hit predicate.")),
                Paragraph(Text(
                    "The universal_exists construction supplies one fixed u with output equal to the "
                        + "singleton image of the standard program e on input zero. The final theorem "
                        + "combines that universal property, total computability of pulse, the operational "
                        + "clock equations, the sharp one-state and t+2 minima, and both nonexistence "
                        + "claims. No finite proxy, bounded prefix assumption, or computable selector is "
                        + "introduced.")))),
            new DocumentBlock.Section(H("Four-slot audit boundary"), Blocks(
                Paragraph(Text(
                    "The public D5 audit targets are single_start_dp_sizes, uniform_single_pulse_obstruction, "
                        + "step_decode, first_terminal, and original_section_6_4, with the public supporting "
                        + "definitions unarySizes, prefixHit, ExhaustiveZeroPrefix, MinimumStateBound, "
                        + "decodeCode, encodeCode, decodeStack, decodeCfg, normal, returning, step, initial, "
                        + "run, pulse, view, normalDispatch, normalBody, returnFrame, and returnBody.")),
                Paragraph(Text(
                    "A same-delivery four-slot registration attempt remains unfinished. No faithful "
                        + "compiled Contract.Registration or current source-occurrence binding is retained "
                        + "for any of the five theorem targets. Missing evidence comprises the complete-telescope "
                        + "realization and source reconstruction, a lawful enrolled readout, and compiled "
                        + "variation, sensitivity, and observational-dependence proofs. The concrete report is "
                        + "https://github.com/the-omega-institute/trureturing/issues/20665. This missing "
                        + "evidence does not establish that the enrolled dependent-family interfaces cannot "
                        + "represent the source theorem. No declared_validated status is asserted; the issue "
                        + "is neither a proof nor a registration result.")))),
            Describe.Lean(
                DescribeId.Create("actual-first-termination-root"),
                DeclarationHandle.Create(Owner + "original_section_6_4"),
                H("A fixed universal program has exact first-termination memory behavior"),
                StatementSource.FromAuthor(OriginalSectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is one fixed universal code u. For every natural program index e, "
                            + "decodeCode u on the one-element input [e] is the singleton image of the "
                            + "standard Nat.Partrec code of e on input zero.")),
                    Paragraph(Text(
                        "The pulse is total computable. The displayed run_decode clause preserves the "
                            + "actual ToPartrec.step at every e and n, including the Option terminal "
                            + "case. The first-terminal clause records both the terminal witness at t "
                            + "and the falsity of every earlier pulse; pulse u 0 0 is true.")),
                    Paragraph(Text(
                        "For every e, an all-false stream has minimum one, a unique hit at t has minimum "
                            + "t+2, and a minimum is attained. The last two clauses exclude both a total "
                            + "computable bound on all attained minima and a total computable inclusive "
                            + "zero-prefix cutoff. These are the exact operational-clock conclusions "
                            + "of the source theorem."))),
                DescribeRole.Theorem))));

    private static Formula OriginalSectionFormula()
    {
        Formula u = F.Id("u"), e = F.Id("e"), n = F.Id("n"), t = F.Id("t");
        Formula q = F.Id("q"), s = F.Id("s"), N = F.Id("N"), k = F.Id("k");
        Formula code = F.Id("Code");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula cfg = Named("Cfg");
        Formula decode = Call("decodeCode", u);
        Formula run = Call("run", u, e, n);
        Formula initial = Call("initial", u, e);
        Formula qStep = Qualified("Turing", "ToPartrec", "step");
        Formula qType = Call("Option", Qualified("Turing", "ToPartrec", "Cfg"));
        Formula clockStep = Seq(Open, F.Id("fun"), Sp, q, Colon, Sp, qType,
            Sp, Mapsto, Sp, Call("bind", q, qStep), Close);
        Formula singletonEval = Call("map", Named("singleton"),
            Call("eval", Call("ofNatCode", e), D(0)));
        Formula universal = All("e", nat,
            Eq(Call("eval", decode, List(e)), singletonEval));
        Formula computablePulse = Seq(
            Operatorname, Grp(F.Id("Computable")), Underscore, Num(2),
            Open, Call("pulse", u), Close);
        Formula iteration = Call("iterate", clockStep, n,
            Call("some", Call("decodeCfg", initial)));
        Formula clock = All("e", nat, All("n", nat,
            Eq(MethodMap(run, Named("decodeCfg")), iteration)));
        Formula first = All("e", nat, All("t", nat,
            Iff(
                Eq(Call("pulse", u, e, t), F.Id("true")),
                And(
                    Ex("q", cfg,
                        And(Eq(Call("run", u, e, t), Call("some", q)),
                            Eq(Call("step", q), F.Id("none")))),
                    All("n", nat,
                        Imp(Less(n, t),
                            Eq(Call("pulse", u, e, n), F.Id("false"))))))));
        Formula zero = Eq(Call("pulse", u, D(0), D(0)), F.Id("true"));
        Formula zeroMinimum = All("e", nat,
            Imp(
                All("n", nat, Eq(Call("pulse", u, e, n), F.Id("false"))),
                Call("IsLeast", Call("unarySizes", Call("pulse", u, e)), D(1))));
        Formula hitMinimum = All("e", nat, All("t", nat,
            Imp(
                Eq(Call("pulse", u, e, t), F.Id("true")),
                Call("IsLeast", Call("unarySizes", Call("pulse", u, e)),
                    Seq(t, Plus, D(2))))));
        Formula attained = All("e", nat,
            Ex("k", nat, Call("IsLeast", Call("unarySizes", Call("pulse", u, e)), k)));
        Formula noBound = new Formula.Not(
            Ex("s", Arrow(nat, nat),
                And(Computable(s), Call("MinimumStateBound", Call("pulse", u), s))));
        Formula noCutoff = new Formula.Not(
            Ex("N", Arrow(nat, nat),
                And(Computable(N), Call("ExhaustiveZeroPrefix", Call("pulse", u), N))));

        return Disp(Ex("u", code,
            AndChain(universal, computablePulse, clock, first, zero,
                zeroMinimum, hitMinimum, attained, noBound, noCutoff)));
    }

    private static Formula List(Formula value) => Seq(OpenBracket, value, CloseBracket);

    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Qualified(params string[] names)
    {
        var items = new List<Formula>();
        for (var index = 0; index < names.Length; index++)
        {
            if (index > 0)
                items.Add(Dot);
            items.Add(F.Id(names[index]));
        }

        return Seq([.. items]);
    }

    private static Formula MethodMap(Formula value, Formula function) =>
        Seq(value, Dot, F.Id("map"), Sp, function);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
                items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula AndChain(params Formula[] values)
    {
        Formula result = values[0];
        for (var index = 1; index < values.Length; index++)
            result = And(result, values[index]);
        return result;
    }

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Computable(Formula value) =>
        Call("Computable", value);

    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.TypeArrow(left, right);
}
