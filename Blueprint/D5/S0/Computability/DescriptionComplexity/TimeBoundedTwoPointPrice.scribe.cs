using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class TimeBoundedTwoPointPriceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite bounded search constructs a target with incomparable fast-long and short-slow witnesses.",
        H("Time-Bounded Two-Point Price Frontier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("time-bounded-two-point-price-frontier"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/TimeBoundedTwoPointPrice."
                    + "time_bounded_two_point_price_frontier"),
                H("Bounded diagonalization forces a two-point price frontier"),
                StatementSource.FromAuthor(FrontierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each length l at least two, diagonalWord is the least binary word "
                        + "outside the bounded-time outputs of all programs of length at most "
                        + "floor(l/2). There are exactly 2^(floor(l/2)+1)-1 such programs, fewer "
                        + "than the 2^l targets, so the finite complement is nonempty.")),
                    Paragraph(Text(
                        "The bounded evaluators are total functions. Decidable witness equality "
                        + "makes each fixed-length program layer finite and searchable, while "
                        + "encodeWitness supplies a terminating upper bound. Thus KBounded is an "
                        + "executable least description length rather than a classical infimum.")),
                    Paragraph(Text(
                        "A fixed-overhead compiler sends any fast valid witness description to a "
                        + "bounded description of its target. Escape from every half-length code "
                        + "therefore gives the displayed half-length lower bound. The explicit "
                        + "quarter-margin condition makes its contrapositive say that every "
                        + "eventually quarter-short witness is slow.")),
                    Paragraph(Text(
                        "The machine interface supplies concrete table and enumerator codes and "
                        + "their successful bounded runs. Their verified price and time bounds "
                        + "give strict incomparability at every length beyond the common margin.")),
                    Paragraph(Text(
                        "The informal logarithmic time factor is represented by the total natural "
                        + "number expression log_2(t(l)+1), avoiding the zero-input convention. "
                        + "The source's O(log l) loss is replaced by the exact quarter-margin "
                        + "hypothesis used by the proof."))),
                DescribeRole.Theorem)),
        []));

    private static Formula FrontierFormula()
    {
        Formula witnessType = F.Id("Witness"), machine = F.Id("M");
        Formula length = F.Id("l"), code = F.Id("p"), witness = F.Id("u");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula target = Call("diagonalWord", machine, length);
        Formula timeBound = Call("t", machine, length);
        Formula wordBudget = Call("T", machine, length);
        Formula margin = Call("marginIndex", machine);
        Formula table = Call("tableWitness", machine, length);
        Formula enumerator = Call("enumeratorWitness", machine, length);
        Formula Implements(Formula value) =>
            Call("implements", machine, length, value, target);
        Formula Complexity(Formula value) =>
            Call("KBounded", machine, length, value);
        Formula Runtime(Formula value) => Call("runtime", machine, length, value);
        Formula AtLeastTwo() => Seq(length, Sp, Geq, Sp, D(2));
        Formula BeyondMargin() => Seq(
            length, Sp, Geq, Sp, Call("max", D(2), margin));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, witnessType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("DecidableEq", witnessType), CloseBracket, Comma, Sp,
            machine, Colon, Sp, Call("TimePricedMachine", witnessType), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            AtLeastTwo(), Comma, Sp, Forall, Sp, code, Comma, Sp,
            Call("runWord", machine, length, code, wordBudget), Sp, Eq, Sp, target,
            Sp, Rightarrow, Sp,
            length, Sp, Slash, Sp, D(2), Sp, Lt, Sp, Call("length", code), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            AtLeastTwo(), Comma, Sp, Forall, Sp, witness, Comma, Sp,
            Implements(witness), Sp, Land, Sp,
            Runtime(witness), Sp, Leq, Sp, timeBound, Sp, Rightarrow, Sp,
            length, Sp, Slash, Sp, D(2), Sp, Minus, Sp,
            Call("overhead", machine, length), Sp, Leq, Sp,
            Complexity(witness), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            BeyondMargin(), Comma, Sp, Forall, Sp, witness, Comma, Sp,
            Implements(witness), Sp, Land, Sp,
            Complexity(witness), Sp, Leq, Sp,
            length, Sp, Slash, Sp, D(4), Sp, Rightarrow, Sp,
            timeBound, Sp, Lt, Sp, Runtime(witness), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            Implements(table), Sp, Land, Sp,
            Complexity(table), Sp, Leq, Sp, length, Sp, Plus, Sp,
            Call("tableOverhead", machine, length), Sp, Land, Sp,
            Runtime(table), Sp, Leq, Sp, length, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            Implements(enumerator), Sp, Land, Sp,
            Complexity(enumerator), Sp, Leq, Sp, Call("enumeratorCost", machine),
            Sp, Land, Sp, timeBound, Sp, Lt, Sp, Runtime(enumerator), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            BeyondMargin(), Comma, Sp,
            Complexity(enumerator), Sp, Lt, Sp, Complexity(table), Sp, Land, Sp,
            Runtime(table), Sp, Lt, Sp, Runtime(enumerator), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
