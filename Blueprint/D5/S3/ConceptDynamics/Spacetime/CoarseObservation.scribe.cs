using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class CoarseObservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observations of native histories preserve exact signed fiber arithmetic.",
        H("Native Coarse Observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-finite-observation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe"),
                H("Full current and selected fibers on every bin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bin map is defined on the entire current-event subtype of an actual three-dimensional history. The output consists of background and selected integer arrays on the whole finite bin type. Unhit bins and signed cancellation remain present. These arrays carry no new causal history, spatial positions or source trees."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("background-total"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_backgroundBins"),
                H("The background array sums to current charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite fiber summation counts every current occurrence exactly once. An empty bin type is allowed when the current region is empty, even if the retained archive is nonempty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("selected-total"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_selectedBins"),
                H("The selected array sums to the arithmetic readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected array uses the existing signed contribution and actual selection. Its total is the same integer readout as that of the rich representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affine-complement"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_complement"),
                H("Selection complement subtracts from the background array"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal event complement keeps the background array and replaces the selected array by background minus selected charge. Global balance alone does not make every background bin zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("successive-pushforwards"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.pushforward_comp"),
                H("Successive finite merging composes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer indicator summation proves composition for both arrays without injectivity or surjectivity assumptions on either merging map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-coarsening"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_coarsen"),
                H("Coarsening agrees with observing through the composite map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each composite bin is the signed sum of its constituent original bins. The bin map remains defined only on current events; archived noncurrent events receive no default bin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parallel-tagged"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_tagged_charges"),
                H("Tagged parallel bins retain the two arrays separately"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual parallel archive tags both inputs. Its current and selected fibers copy the corresponding left and right fibers, even when the input archives use equal event names."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parallel-common"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_common_charges"),
                H("Common parallel bins add the two arrays"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Merging left and right tags into a shared bin type gives pointwise addition of both background and selected charges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-product-fiber"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.generated_selected_bin_fiber"),
                H("Each generated bin fiber retains ordered parent occurrences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected fiber in the new generated current is the image of the Cartesian product of the two input selected fibers. Equal sources and cancellation never identify distinct ordered parent pairs. Both old archives remain retained outside the new current."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-product-charges"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_bin_charges"),
                H("The actual generated product multiplies both bin arrays"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the native generated charge through its ordered parent fibers yields the product of the corresponding background charges and of the corresponding selected charges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coarsened-product-charges"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_coarsened_charges"),
                H("Arbitrary product-bin merging follows the native product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The formula first uses the actual generated product and its parent-bin fiber equation, then pushes both arrays through any map from the product bin type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split-spatial-source-witness"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.two_bin_counterexample"),
                H("A balanced two-event history has nonzero spatial and source bins"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two events have opposite signs, common time zero, empty causal order, distinct leaf sources and distinct first spatial coordinates. Both are current and only the positive event is selected. In positive/negative order the arrays are (1,-1), (1,0), and the complement (0,-1); the complement is not the negative selected array."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global-local-refutation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation.not_global_balance_forces_local_balance"),
                H("Global balance does not force local bin balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed universal claim is refuted by the stated actual two-event history. This establishes the finite-bin counterexample and the arithmetic formulas of Proposition 9; it asserts no continuous physics, whole-theory completion, or ZFC conservativity result."))),
                DescribeRole.Theorem))));
}
