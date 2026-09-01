using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PrimeFourierMagnusCommutatorBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second-Magnus Fourier swap kernel is exactly the scalar coefficient of the two-channel Lie commutator.",
        H("Prime Fourier Magnus Commutator Bridge"),
        Blocks(
            Item("generator", "twoChannelFourierGenerator", "Two-channel Fourier generator",
                "Two fixed Lie generators are modulated by their unitary Fourier characters and added at each time.", DescribeRole.Definition),
            Item("kernel-coefficient", "two_channel_fourier_lie_bracket", "Fourier kernel is the Lie coefficient",
                "The cross-time Lie bracket equals the frozen second-Magnus swap kernel multiplying the cross-channel Lie bracket.", DescribeRole.Theorem),
            Item("equal-time", "two_channel_fourier_lie_bracket_equal_times", "Equal-time vanishing",
                "Evaluating both slots at the same time gives a self bracket and therefore zero curvature.", DescribeRole.Theorem),
            Item("equal-frequency", "two_channel_fourier_lie_bracket_equal_frequencies", "Equal-frequency vanishing",
                "When the two frequencies coincide, the scalar swap kernel vanishes and so does the cross-time Lie curvature.", DescribeRole.Theorem),
            Item("commuting", "two_channel_fourier_lie_bracket_eq_zero_of_commute", "Commuting-channel collapse",
                "Commuting channel generators carry no second-Magnus Lie curvature for any times or frequencies.", DescribeRole.Theorem),
            Item("time-swap", "two_channel_fourier_lie_bracket_swap_time", "Time-slot orientation reversal",
                "Reversing the two time slots negates the complete Lie curvature.", DescribeRole.Theorem),
            Item("log-address", "log_address_two_channel_lie_bracket", "Logarithmic address specialization",
                "Natural and prime addresses specialize the two frequencies to logarithms while preserving the exact kernel coefficient identity.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoFreeLieBridge")),
        ]));

    private static DocumentBlock.Describe Item(
        string id, string declaration, string heading,
        string paragraph, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);
}
