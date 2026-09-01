using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PrimeFourierMagnusCommutatorBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen Fourier swap kernel is exactly the coefficient of represented degree-two free-Lie commutators in a finite matrix generator.",
        H("Prime Fourier Magnus Commutator Bridge"),
        Blocks(
            Entry("generator", "finiteFourierMatrixGenerator",
                "Finite Fourier matrix generator",
                "Fixed channel matrices are weighted by the frozen unitary Fourier characters.", DescribeRole.Definition),
            Entry("weighted-commutator", "finite_weighted_generator_commutator",
                "Weighted commutator expansion",
                "Bilinearity expands the two weighted matrix sums into all pairwise represented Lie brackets.", DescribeRole.Theorem),
            Entry("alternant", "finite_weighted_commutator_alternant",
                "Alternating ordered-product coefficient",
                "Exchanging finite indices in the reversed product isolates the alternating coefficient of each ordered matrix product.", DescribeRole.Theorem),
            Entry("free-lie", "finite_fourier_generator_freeLie_expansion",
                "Free-Lie Fourier expansion",
                "The two-time generator commutator is the Fourier-weighted sum of evaluated degree-two free-Lie brackets.", DescribeRole.Theorem),
            Entry("second-magnus", "finite_fourier_generator_secondMagnus_expansion",
                "Second-Magnus coefficient identity",
                "The ordered-product coefficient is exactly the frozen second-Magnus swap kernel.", DescribeRole.Theorem),
            Entry("commuting-zero", "finite_fourier_generator_commutator_eq_zero_of_pairwise",
                "Pairwise commuting channels have zero Magnus defect",
                "If every fixed channel pair commutes, the complete two-time Fourier commutator vanishes.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoFreeLieBridge"))
        ]));

    private static DocumentBlock.Describe Entry(
        string id, string declaration, string heading, string paragraph,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);
}
