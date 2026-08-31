using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PhaseTwistedStableSwapCurvatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary Fourier phases twist stable memory channels without worsening residual curvature-energy bounds.",
        H("Phase-Twisted Stable Swap Curvature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-twisted-channel"),
                DeclarationHandle.Create(Prefix + "phaseTwistedChannel"),
                H("Phase-twisted memory channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply a complex memory channel by the Fourier phase attached to its "
                        + "frequency at the chosen spectral time."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-twisted-stable-swap-curvature"),
                DeclarationHandle.Create(Prefix + "phaseTwistedStableSwapCurvature"),
                H("Phase-twisted stable swap curvature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluate stable residual swap curvature on the two phase-rotated memory "
                        + "channels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-twisted-stable-holonomy-energy"),
                DeclarationHandle.Create(Prefix + "phaseTwistedStableHolonomyEnergy"),
                H("Phase-twisted finite holonomy energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Aggregate the squared norms of all ordered-pair phase-twisted stable "
                        + "curvatures on a finite carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-twisted-channel-norm"),
                DeclarationHandle.Create(Prefix + "phase_twisted_channel_norm"),
                H("Unitary twisting preserves channel norm"),
                StatementSource.FromAuthor(ChannelNormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real frequency and spectral time, multiplying a complex "
                            + "channel by its Fourier phase preserves the channel norm.")),
                    Paragraph(Text(
                        "The conclusion uses only the unit norm of the individual phase. It "
                            + "does not identify phases at different frequencies or assert "
                            + "phase synchronization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-phase-reconstruction"),
                DeclarationHandle.Create(Prefix + "relative_phase_reconstruction"),
                H("Relative frequency reconstructs channel phase"),
                StatementSource.FromAuthor(RelativePhaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At every spectral time, the phase at the difference of two real "
                            + "frequencies times the second phase equals the first phase.")),
                    Paragraph(Text(
                        "This is the multiplicative character law for Fourier phases. It does "
                            + "not say that the two channel phases or their frequencies are "
                            + "equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-log-address-phase-reconstruction"),
                DeclarationHandle.Create(
                    Prefix + "relative_log_address_phase_reconstruction"),
                H("Logarithmic relative address phase"),
                StatementSource.FromAuthor(RelativeLogAddressPhaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two natural-number addresses, the phase at the difference of "
                            + "their real logarithms reconstructs the first logarithmic "
                            + "address phase from the second.")),
                    Paragraph(Text(
                        "The statement uses Lean's total real logarithm and assumes neither "
                            + "positivity nor primality of the addresses. It supplies no "
                            + "converse or address-identification result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-twisted-curvature-zero-time"),
                DeclarationHandle.Create(Prefix + "phase_twisted_curvature_zero_time"),
                H("Zero time recovers untwisted curvature"),
                StatementSource.FromAuthor(ZeroTimeCurvatureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At spectral time zero, both Fourier twists are the identity, so the "
                            + "phase-twisted stable swap curvature equals the untwisted stable "
                            + "residual swap curvature.")),
                    Paragraph(Text(
                        "This equality is restricted to zero time. It does not make curvature "
                            + "time-independent and gives no monotonicity or decay away from "
                            + "zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-twisted-stable-swap-curvature-bound"),
                DeclarationHandle.Create(
                    Prefix + "phase_twisted_stable_swap_curvature_bound"),
                H("Time-uniform pairwise residual curvature bound"),
                StatementSource.FromAuthor(PairwiseCurvatureBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assuming each of the two channel norms is at most one, the twisted "
                            + "curvature has the displayed linear-bilinear residual expansion "
                            + "and the corresponding pairwise norm bound.")),
                    Paragraph(Text(
                        "For every nonnegative envelope bounding both residual norms, the "
                            + "stated quadratic envelope estimate follows uniformly in the "
                            + "chosen time. This norm estimate asserts no phase synchronization, "
                            + "time monotonicity, or residual decay."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-twisted-finite-holonomy-energy-bound"),
                DeclarationHandle.Create(
                    Prefix + "phase_twisted_finite_holonomy_energy_bound"),
                H("Time-uniform finite holonomy-energy bound"),
                StatementSource.FromAuthor(FiniteEnergyBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite carrier, a nonnegative residual envelope together with "
                            + "the stated pointwise channel and residual bounds makes the "
                            + "twisted holonomy energy nonnegative and bounds it by the "
                            + "cardinality-square expression.")),
                    Paragraph(Text(
                        "The energy is zero exactly when every ordered-pair twisted curvature "
                            + "vanishes, and a zero envelope forces zero energy. These finite, "
                            + "time-uniform facts imply no phase synchronization, residual "
                            + "decay, zero-location theorem, or RH conclusion."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Named(Formula name) =>
        Seq(Operatorname, Grp(name));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula FourierPhase(
        Formula frequency, Formula time) =>
        Apply(Named(F.Id("fourierPhase")), frequency, time);

    private static Formula TwistedChannel(
        Formula frequency, Formula time, Formula channel) =>
        Apply(Named(F.Id("phaseTwistedChannel")), frequency, time, channel);

    private static Formula TwistedCurvature(
        Formula stable,
        Formula residualP,
        Formula residualQ,
        Formula channelP,
        Formula channelQ,
        Formula frequencyP,
        Formula frequencyQ,
        Formula time) =>
        Apply(
            Named(F.Id("phaseTwistedStableSwapCurvature")),
            stable,
            residualP,
            residualQ,
            channelP,
            channelQ,
            frequencyP,
            frequencyQ,
            time);

    private static Formula ChannelNormFormula()
    {
        Formula frequency = F.Id("omega");
        Formula time = F.Id("t");
        Formula channel = F.Id("v");

        return Disp(Seq(
            Forall, Sp, frequency, Comma, Sp, time,
            Colon, Sp, Reals(), Comma, Sp,
            channel, Colon, Sp, Complexes(), Comma, RowBreak, Grp(),
            Norm(TwistedChannel(frequency, time, channel)),
            Sp, Eq, Sp, Norm(channel), Dot));
    }

    private static Formula RelativePhaseFormula()
    {
        Formula frequencyP = new Formula.Subscript(F.Id("omega"), F.Id("p"));
        Formula frequencyQ = new Formula.Subscript(F.Id("omega"), F.Id("q"));
        Formula time = F.Id("t");
        Formula difference = Seq(
            frequencyP, Sp, Minus, Sp, frequencyQ);

        return Disp(Seq(
            Forall, Sp, frequencyP, Comma, Sp, frequencyQ, Comma, Sp, time,
            Colon, Sp, Reals(), Comma, RowBreak, Grp(),
            FourierPhase(difference, time), Sp, Cdot, Sp,
            FourierPhase(frequencyQ, time),
            Sp, Eq, Sp, FourierPhase(frequencyP, time), Dot));
    }

    private static Formula RelativeLogAddressPhaseFormula()
    {
        Formula addressP = new Formula.Subscript(F.Id("n"), F.Id("p"));
        Formula addressQ = new Formula.Subscript(F.Id("n"), F.Id("q"));
        Formula time = F.Id("t");
        Formula logP = Apply(Named(F.Id("log")), addressP);
        Formula logQ = Apply(Named(F.Id("log")), addressQ);
        Formula logDifference = Seq(logP, Sp, Minus, Sp, logQ);
        Formula logAddressPhase = Named(F.Id("logAddressPhase"));

        return Disp(Seq(
            Forall, Sp, addressP, Comma, Sp, addressQ,
            Colon, Sp, Naturals(), Comma, Sp,
            time, Colon, Sp, Reals(), Comma, RowBreak, Grp(),
            FourierPhase(logDifference, time), Sp, Cdot, Sp,
            Apply(logAddressPhase, addressQ, time),
            Sp, Eq, Sp, Apply(logAddressPhase, addressP, time), Dot));
    }

    private static Formula ZeroTimeCurvatureFormula()
    {
        Formula stable = F.Id("a");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula residualQ = new Formula.Subscript(F.Id("r"), F.Id("q"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula channelQ = new Formula.Subscript(F.Id("v"), F.Id("q"));
        Formula frequencyP = new Formula.Subscript(F.Id("omega"), F.Id("p"));
        Formula frequencyQ = new Formula.Subscript(F.Id("omega"), F.Id("q"));
        Formula untwistedCurvature = Apply(
            Named(F.Id("stableResidualSwapCurvature")),
            stable, residualP, residualQ, channelP, channelQ);

        return Disp(Seq(
            Forall, Sp,
            stable, Comma, Sp, residualP, Comma, Sp, residualQ, Comma, Sp,
            channelP, Comma, Sp, channelQ,
            Colon, Sp, Complexes(), Comma, RowBreak, Grp(),
            frequencyP, Comma, Sp, frequencyQ,
            Colon, Sp, Reals(), Comma, RowBreak, Grp(),
            TwistedCurvature(
                stable, residualP, residualQ, channelP, channelQ,
                frequencyP, frequencyQ, D(0)),
            Sp, Eq, Sp, untwistedCurvature, Dot));
    }

    private static Formula PairwiseCurvatureBoundFormula()
    {
        Formula stable = F.Id("a");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula residualQ = new Formula.Subscript(F.Id("r"), F.Id("q"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula channelQ = new Formula.Subscript(F.Id("v"), F.Id("q"));
        Formula frequencyP = new Formula.Subscript(F.Id("omega"), F.Id("p"));
        Formula frequencyQ = new Formula.Subscript(F.Id("omega"), F.Id("q"));
        Formula time = F.Id("t");
        Formula envelope = Varepsilon;
        Formula twistedP = TwistedChannel(frequencyP, time, channelP);
        Formula twistedQ = TwistedChannel(frequencyQ, time, channelQ);
        Formula curvature = TwistedCurvature(
            stable, residualP, residualQ, channelP, channelQ,
            frequencyP, frequencyQ, time);
        Formula stableGap = Seq(Open, stable, Sp, Minus, Sp, D(1), Close);
        Formula exactValue = Seq(
            stableGap, Sp, Cdot, Sp,
            Open,
            residualP, Sp, Cdot, Sp, twistedP,
            Sp, Minus, Sp,
            residualQ, Sp, Cdot, Sp, twistedQ,
            Close,
            Sp, Plus, Sp,
            residualP, Sp, Cdot, Sp, residualQ, Sp, Cdot, Sp,
            Open, twistedQ, Sp, Minus, Sp, twistedP, Close);
        Formula normBound = Seq(
            Norm(stableGap), Sp, Cdot, Sp,
            Open, Norm(residualP), Sp, Plus, Sp, Norm(residualQ), Close,
            Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Norm(residualP), Sp, Cdot, Sp, Norm(residualQ));
        Formula envelopeBound = Seq(
            D(2), Sp, Cdot, Sp, Norm(stableGap), Sp, Cdot, Sp, envelope,
            Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Power(envelope, D(2)));
        Formula channelPremises = Seq(
            Norm(channelP), Sp, Leq, Sp, D(1),
            Sp, Land, Sp,
            Norm(channelQ), Sp, Leq, Sp, D(1));
        Formula envelopePremises = Seq(
            D(0), Sp, Leq, Sp, envelope,
            Sp, Land, Sp,
            Norm(residualP), Sp, Leq, Sp, envelope,
            Sp, Land, Sp,
            Norm(residualQ), Sp, Leq, Sp, envelope);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stable, Comma, Sp, residualP, Comma, Sp, residualQ, Comma, Sp,
            channelP, Comma, Sp, channelQ,
            Colon, Sp, Complexes(), Comma, RowBreak, Grp(),
            frequencyP, Comma, Sp, frequencyQ, Comma, Sp, time,
            Colon, Sp, Reals(), Comma, RowBreak, Grp(),
            Open, channelPremises, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open,
            Open, curvature, Sp, Eq, Sp, exactValue, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Norm(curvature), Sp, Leq, Sp, normBound, Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            Forall, Sp, envelope, Colon, Sp, Reals(), Comma, Sp,
            Open, envelopePremises, Close, Sp, Rightarrow, Sp,
            Norm(curvature), Sp, Leq, Sp, envelopeBound,
            Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteEnergyBoundFormula()
    {
        Formula carrier = Iota;
        Formula stable = F.Id("a");
        Formula residual = F.Id("r");
        Formula channel = F.Id("v");
        Formula frequency = F.Id("omega");
        Formula time = F.Id("t");
        Formula envelope = Varepsilon;
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula energy = F.Id("E");
        Formula carrierType = Named(F.Id("Type"));
        Formula complexFamily = new Formula.TypeArrow(carrier, Complexes());
        Formula realFamily = new Formula.TypeArrow(carrier, Reals());
        Formula energyValue = Apply(
            Named(F.Id("phaseTwistedStableHolonomyEnergy")),
            stable, residual, channel, frequency, time);
        Formula residualAtP = Apply(residual, p);
        Formula residualAtQ = Apply(residual, q);
        Formula channelAtP = Apply(channel, p);
        Formula channelAtQ = Apply(channel, q);
        Formula frequencyAtP = Apply(frequency, p);
        Formula frequencyAtQ = Apply(frequency, q);
        Formula curvature = TwistedCurvature(
            stable,
            residualAtP,
            residualAtQ,
            channelAtP,
            channelAtQ,
            frequencyAtP,
            frequencyAtQ,
            time);
        Formula stableGap = Seq(Open, stable, Sp, Minus, Sp, D(1), Close);
        Formula pairwiseBound = Seq(
            D(2), Sp, Times, Sp, Norm(stableGap),
            Sp, Times, Sp, envelope,
            Sp, Plus, Sp,
            D(2), Sp, Times, Sp, Power(envelope, D(2)));
        Formula realCardinality = new Formula.Subscript(
            Named(F.Id("card")), Reals());
        Formula energyBound = Seq(
            Apply(realCardinality, carrier), Caret, Grp(D(2)),
            Sp, Times, Sp,
            Open, pairwiseBound, Close, Caret, Grp(D(2)));
        Formula channelBound = Seq(
            Forall, Sp, p, Colon, Sp, carrier, Comma, Sp,
            Norm(channelAtP), Sp, Leq, Sp, D(1));
        Formula residualBound = Seq(
            Forall, Sp, p, Colon, Sp, carrier, Comma, Sp,
            Norm(residualAtP), Sp, Leq, Sp, envelope);
        Formula premises = Seq(
            D(0), Sp, Leq, Sp, envelope,
            Sp, Land, Sp, Open, channelBound, Close,
            Sp, Land, Sp, Open, residualBound, Close);
        Formula zeroCriterion = Seq(
            Open, energy, Sp, Eq, Sp, D(0), Close,
            Sp, Iff, Sp,
            Open,
            Forall, Sp, p, Comma, Sp, q, Colon, Sp, carrier, Comma, Sp,
            curvature, Sp, Eq, Sp, D(0),
            Close);
        Formula zeroEnvelope = Seq(
            envelope, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            energy, Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Colon, Sp, carrierType, Comma, Sp,
            OpenBracket, Named(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            stable, Colon, Sp, Complexes(), Comma, Sp,
            residual, Comma, Sp, channel, Colon, Sp, complexFamily, Comma, Sp,
            frequency, Colon, Sp, realFamily, Comma, RowBreak, Grp(),
            time, Comma, Sp, envelope, Colon, Sp, Reals(), Comma,
            RowBreak, Grp(),
            Open, premises, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            energy, Sp, Colon, Eq, Sp, energyValue, Comma,
            RowBreak, Grp(),
            Open,
            Open, D(0), Sp, Leq, Sp, energy, Close,
            Sp, Land, RowBreak, Grp(),
            Open, energy, Sp, Leq, Sp, energyBound, Close,
            Sp, Land, RowBreak, Grp(),
            Open, zeroCriterion, Close,
            Sp, Land, RowBreak, Grp(),
            Open, zeroEnvelope, Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
