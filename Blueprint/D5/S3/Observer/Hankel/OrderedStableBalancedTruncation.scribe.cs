using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class OrderedStableBalancedTruncationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same constructed largest-singular-weight reduced model is strictly internally stable and obeys both tail-sum error bounds.",
        H("Ordered Stable Balanced Truncation"),
        Blocks(
            Describe.Lean(DescribeId.Create("future-readout"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_future_readout"), H("Transport every future readout"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves the complete matrix readout identity through all powers of the actual balanced transition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-observability"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_full_observable"), H("Inherited full observation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves joint readout injectivity for the full balanced realization using original-system observability and both inverse coordinate maps. Reduced observability is not assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-system-coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.orderedSystemCoordinates"), H("Construct ordered system coordinates"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs actual infinite Gramians and balancing maps, then applies the same descending permutation to the weights and state coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-schmidt"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_hankel_schmidt"), H("Ordered genuine Hankel singular modes"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sorted positive weights retain the actual infinite Hankel orthonormal modes, both singular-vector equations, complete expansion and kernel characterization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-stability"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_spectrum_lt_one"), H("Strict stability of the actual ordered cut"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives all complex poles of the actual largest-weight prefix model inside the open unit disk from original-system hypotheses. Repeated weights and empty cuts are included without an assumed gap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-window-error"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_window_bound"), H("Ordered finite-window tail bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identical constructed ordered model satisfies the original-system finite-window error bound with the discarded singular tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-l2-error"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_l2_bound"), H("Ordered infinite-energy tail bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the identical model, proves error-energy summability and the infinite-time tail-sum error estimate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-stable-reduction"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_stable_reduction"), H("Single-model ordered stable reduction theorem"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One construction simultaneously retains the largest weights, is strictly stable in the standard complex spectrum, and satisfies both finite-window and whole-half-line error bounds. All clauses reference the same state, input and output matrices."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/OrderedBalancedCoordinates")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/DiscreteSteinCompressionStability"))]));
}
