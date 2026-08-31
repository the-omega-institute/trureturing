using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedPrimeMemoryCocycleDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier-timed prime events form an affine memory cocycle whose swap defect is prime curvature.",
        H("Time-Ordered Prime Memory Cocycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("timed-prime-memory-event"),
                DeclarationHandle.Create(Prefix + "TimedPrimeMemoryEvent"),
                H("Timed prime memory event"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A local event stores a scalar factor, a base memory injection, a real "
                        + "frequency, and a real Fourier time. Prime channels are obtained by "
                        + "using logarithmic prime frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-ordered-memory-cocycle"),
                DeclarationHandle.Create(Prefix + "timeOrderedMemoryCocycle"),
                H("Time-ordered memory cocycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The memory summary weights an earlier event by the stable powers of all "
                        + "later slots and by the scalar factors accumulated before later "
                        + "injections. It is normalized at zero initial memory and unit scalar "
                        + "input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-ordered-evolution"),
                DeclarationHandle.Create(Prefix + "timeOrderedEvolution"),
                H("Chronological affine evolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The event list acts from left to right. The list head acts first, so list "
                        + "order is an operational chronology distinct from the real Fourier "
                        + "time stored in each event."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("timed-injection-shift"),
                DeclarationHandle.Create(Prefix + "timed_injection_shift"),
                H("Fourier time translation of an injection"),
                StatementSource.FromAuthor(InjectionShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Shifting the event time multiplies its effective injection by the Fourier "
                        + "character of the shift. This imports the additive time-character law "
                        + "without adding an arrow of time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-evolution-affine"),
                DeclarationHandle.Create(Prefix + "time_ordered_evolution_affine"),
                H("Exact affine word action"),
                StatementSource.FromAuthor(AffineActionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finite chronological word acts by a stable power on initial memory, "
                        + "the time-ordered memory cocycle on scalar input, and the commutative "
                        + "scalar word on the scalar coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-cocycle-append-laws"),
                DeclarationHandle.Create(Prefix + "time_ordered_cocycle_append_laws"),
                H("Twisted cocycle law under concatenation"),
                StatementSource.FromAuthor(AppendLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Scalar summaries multiply under list concatenation. Memory summaries "
                            + "obey the twisted law in which the suffix length transports the "
                            + "prefix memory by a stable power and the prefix scalar transports "
                            + "the suffix memory.")),
                    Paragraph(Text(
                        "The full affine evolution of a concatenated list is the composition of "
                            + "the prefix evolution followed by the suffix evolution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-ordered-two-event-swap-curvature"),
                DeclarationHandle.Create(Prefix + "time_ordered_two_event_swap_curvature"),
                H("Two-event chronology defect"),
                StatementSource.FromAuthor(TwoEventSwapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing two timed events leaves the scalar coordinate unchanged. The "
                        + "memory-coordinate difference is exactly the gauge-invariant prime "
                        + "swap curvature evaluated on their Fourier-rotated injections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("timed-residual-two-event-swap"),
                DeclarationHandle.Create(Prefix + "timed_residual_two_event_swap"),
                H("Residual chronology with independent event times"),
                StatementSource.FromAuthor(ResidualSwapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For residual local factors at possibly different Fourier times, the "
                        + "chronology defect is stable residual curvature evaluated on the two "
                        + "independently phase-rotated channels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-time-residual-swap"),
                DeclarationHandle.Create(
                    Prefix + "common_time_residual_swap_recovers_phase_twisted_curvature"),
                H("Recovery of the common-time phase-twisted curvature"),
                StatementSource.FromAuthor(CommonTimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the two event times coincide, the list-level chronology defect "
                        + "specializes exactly to the existing common-time phase-twisted stable "
                        + "swap curvature."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature")),
        ]));

    private static Formula ComplexNumbers() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ListOf(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);

    private static Formula LengthOf(Formula list) =>
        Seq(Lvert, Sp, list, Sp, Rvert);

    private static Formula PowerOf(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula InjectionShiftFormula()
    {
        Formula e = F.Id("e");
        Formula shift = F.Id("s");
        return Disp(Seq(
            Forall, Sp, e, Comma, Sp, shift, Colon, Sp, Reals(), Comma, Sp,
            Call("timedInjection", Call("shiftTimedEvent", shift, e)),
            Sp, Eq, Sp,
            Call("timedInjection", e), Sp, Cdot, Sp,
            Call("fourierPhase", Call("frequency", e), shift), Dot));
    }

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula AffineActionFormula()
    {
        Formula stable = F.Id("s");
        Formula events = F.Id("L");
        Formula state = F.Id("x");
        return Disp(Seq(
            Forall, Sp, stable, Colon, Sp, ComplexNumbers(), Comma, Sp,
            events, Comma, Sp, state, Comma, Sp,
            Call("timeOrderedEvolution", stable, events, state), Sp, Eq, Sp,
            Open,
            PowerOf(stable, LengthOf(events)), Sp, Cdot, Sp,
            Call("fst", state), Sp, Plus, Sp,
            Call("timeOrderedMemoryCocycle", stable, events), Sp, Cdot, Sp,
            Call("snd", state), Comma, Sp,
            Call("timeOrderedScalarCocycle", events), Sp, Cdot, Sp,
            Call("snd", state),
            Close, Dot));
    }

    private static Formula AppendLawsFormula()
    {
        Formula stable = F.Id("s");
        Formula prefix = F.Id("P");
        Formula suffix = F.Id("S");
        Formula state = F.Id("x");
        Formula joined = Call("append", prefix, suffix);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stable, Colon, Sp, ComplexNumbers(), Comma, Sp,
            prefix, Comma, Sp, suffix, Colon,
            RowBreak, Grp(),
            Call("timeOrderedScalarCocycle", joined), Sp, Eq, Sp,
            Call("timeOrderedScalarCocycle", prefix), Sp, Cdot, Sp,
            Call("timeOrderedScalarCocycle", suffix), Sp, Land,
            RowBreak, Grp(),
            Call("timeOrderedMemoryCocycle", stable, joined), Sp, Eq, Sp,
            PowerOf(stable, LengthOf(suffix)), Sp, Cdot, Sp,
            Call("timeOrderedMemoryCocycle", stable, prefix), Sp, Plus, Sp,
            Call("timeOrderedMemoryCocycle", stable, suffix), Sp, Cdot, Sp,
            Call("timeOrderedScalarCocycle", prefix), Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp,
            Call("timeOrderedEvolution", stable, joined, state), Sp, Eq, Sp,
            Call("timeOrderedEvolution", stable, suffix,
                Call("timeOrderedEvolution", stable, prefix, state)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TwoEventSwapFormula()
    {
        Formula stable = F.Id("s");
        Formula eventP = F.Id("P");
        Formula eventQ = F.Id("Q");
        Formula state = F.Id("x");
        Formula forward = ListOf(eventP, eventQ);
        Formula reversed = ListOf(eventQ, eventP);
        Formula curvature = Call("primeSwapCurvature", stable,
            Call("timedInjection", eventP), Call("localFactor", eventP),
            Call("timedInjection", eventQ), Call("localFactor", eventQ));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stable, Colon, Sp, ComplexNumbers(), Comma, Sp,
            eventP, Comma, Sp, eventQ, Comma, Sp, state, Colon,
            RowBreak, Grp(),
            Call("fst", Call("timeOrderedEvolution", stable, forward, state)),
            Sp, Minus, Sp,
            Call("fst", Call("timeOrderedEvolution", stable, reversed, state)),
            Sp, Eq, Sp, curvature, Sp, Cdot, Sp, Call("snd", state), Sp, Land,
            RowBreak, Grp(),
            Call("snd", Call("timeOrderedEvolution", stable, forward, state)),
            Sp, Eq, Sp,
            Call("snd", Call("timeOrderedEvolution", stable, reversed, state)),
            Sp, Land,
            RowBreak, Grp(),
            Call("timeOrderedMemoryCocycle", stable, forward), Sp, Minus, Sp,
            Call("timeOrderedMemoryCocycle", stable, reversed), Sp, Eq, Sp,
            curvature, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ResidualEvent(
        Formula residual, Formula channel, Formula frequency, Formula time) =>
        Call("residualTimedEvent", residual, channel, frequency, time);

    private static Formula ResidualSwapFormula()
    {
        Formula stable = F.Id("s");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula residualQ = new Formula.Subscript(F.Id("r"), F.Id("q"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula channelQ = new Formula.Subscript(F.Id("v"), F.Id("q"));
        Formula frequencyP = new Formula.Subscript(F.Id("f"), F.Id("p"));
        Formula frequencyQ = new Formula.Subscript(F.Id("f"), F.Id("q"));
        Formula timeP = new Formula.Subscript(F.Id("t"), F.Id("p"));
        Formula timeQ = new Formula.Subscript(F.Id("t"), F.Id("q"));
        Formula eventP = ResidualEvent(residualP, channelP, frequencyP, timeP);
        Formula eventQ = ResidualEvent(residualQ, channelQ, frequencyQ, timeQ);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("timeOrderedMemoryCocycle", stable, ListOf(eventP, eventQ)),
            Sp, Minus, Sp,
            Call("timeOrderedMemoryCocycle", stable, ListOf(eventQ, eventP)),
            RowBreak, Grp(),
            Eq, Sp, Call("stableResidualSwapCurvature", stable,
                residualP, residualQ,
                Call("phaseTwistedChannel", frequencyP, timeP, channelP),
                Call("phaseTwistedChannel", frequencyQ, timeQ, channelQ)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CommonTimeFormula()
    {
        Formula stable = F.Id("s");
        Formula time = F.Id("t");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula residualQ = new Formula.Subscript(F.Id("r"), F.Id("q"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula channelQ = new Formula.Subscript(F.Id("v"), F.Id("q"));
        Formula frequencyP = new Formula.Subscript(F.Id("f"), F.Id("p"));
        Formula frequencyQ = new Formula.Subscript(F.Id("f"), F.Id("q"));
        Formula eventP = ResidualEvent(residualP, channelP, frequencyP, time);
        Formula eventQ = ResidualEvent(residualQ, channelQ, frequencyQ, time);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("timeOrderedMemoryCocycle", stable, ListOf(eventP, eventQ)),
            Sp, Minus, Sp,
            Call("timeOrderedMemoryCocycle", stable, ListOf(eventQ, eventP)),
            RowBreak, Grp(),
            Eq, Sp, Call("phaseTwistedStableSwapCurvature", stable,
                residualP, residualQ, channelP, channelQ,
                frequencyP, frequencyQ, time), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
