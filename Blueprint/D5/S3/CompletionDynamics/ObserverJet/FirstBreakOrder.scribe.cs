using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class FirstBreakOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first nonzero normal jet order is totalized in WithTop Nat, with infinity recording threads whose every finite jet remains unbroken.",
        H("First Break Order"),
        Blocks(
            Theorem(
                "first-break-order-eq-top-iff",
                "first_break_order_eq_top_iff",
                "First Break Order eq Top iff",
                "Absence of every positive finite break is represented exactly by ⊤.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-break-order-of-exists",
                "first_break_order_of_exists",
                "First Break Order Of Exists",
                "Under an existence witness, the totalized order is the ordinary least natural-number witness.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-break-order-spec",
                "first_break_order_spec",
                "First Break Order Spec",
                "The selected finite order is a genuine positive break.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-break-before-first",
                "no_break_before_first",
                "No Break Before First",
                "No smaller order is an admissible break.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-order-break-characterization",
                "first_order_break_characterization",
                "First Order Break Characterization",
                "A first-order break means that order one is the least positive nonzero jet.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-break-characterization",
                "quadratic_break_characterization",
                "Quadratic Break Characterization",
                "If order one vanishes and order two breaks, the first break is quadratic.",
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
