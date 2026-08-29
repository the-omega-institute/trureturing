using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.DynamicReal;

internal sealed class CompletionThreadFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/DynamicReal/CompletionThreadFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant completed readout has a nontrivial thread fiber, while adjoining the blow-up origin restores injectivity and proves that no completed-value decoder can reconstruct every thread.",
        H("Completion Thread Fiber"),
        Blocks(
            Theorem(
                "completion-value-constant",
                "completion_value_constant",
                "Completion Value Constant",
                "Every pair of threads lies in the same zeroth-order completion fiber.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-value-not-injective",
                "completion_value_not_injective",
                "Completion Value Not Injective",
                "Zeroth-order completion is not injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "blowup-value-injective",
                "blowup_value_injective",
                "Blowup Value Injective",
                "The first blow-up readout is injective on this normalized thread family.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completed-jet-readout-injective",
                "completed_jet_readout_injective",
                "Completed Jet Readout Injective",
                "Adjoining the first jet to the completion value restores injectivity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-completion-value-decoder",
                "no_completion_value_decoder",
                "No Completion Value Decoder",
                "No function of the completed value alone can recover every origin coefficient.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-completion-thread-reconstructor",
                "no_completion_thread_reconstructor",
                "No Completion Thread Reconstructor",
                "Any putative reconstruction of the full normalized observer from the completed value would induce a forbidden origin decoder.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-fiber-contains-all-origins",
                "completion_fiber_contains_all_origins",
                "Completion Fiber Contains All Origins",
                "The common completion fiber is infinite, witnessed by the embedding of all real origin coefficients.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
