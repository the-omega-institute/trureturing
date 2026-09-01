using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeFourierMagnusCommutatorBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-channel Fourier commutator is the second-Magnus swap kernel times the interpreted free-Lie bracket.",
        H("Prime Fourier-Magnus Commutator Bridge"),
        Blocks(
            Def("commutator", "matrixCommutator", "Matrix commutator",
                "The noncommutative curvature of two matrix channels is their ordered product difference."),
            Def("generator", "twoChannelFourierGenerator", "Two-channel Fourier generator",
                "Two matrix channels are modulated by their unitary Fourier characters and added."),
            Thm("lie-matrix", "free_lie_degree_two_matrix_lift", "Free-Lie pair maps to matrix commutator",
                "The universal degree-two event word is interpreted as the associative commutator of the two channel matrices."),
            Thm("factorization", "two_channel_fourier_commutator_factorization", "Exact two-channel Magnus factorization",
                "The two-time commutator of the Fourier generator equals the frozen swap kernel times the channel commutator."),
            Thm("free-lie", "two_channel_fourier_commutator_free_lie", "Fourier kernel is the free-Lie coefficient",
                "The same factorization is expressed directly through the universal free-Lie degree-two word."),
            Thm("equal-time", "two_channel_fourier_commutator_equal_time", "Equal times erase the response",
                "Coincident time slots force the second-Magnus matrix commutator to vanish."),
            Thm("commuting-zero", "two_channel_fourier_commutator_eq_zero_of_channels_commute", "Commuting channels erase the response",
                "If the two channel matrices commute, every two-time Fourier-Magnus commutator vanishes.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoFreeLieBridge")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
