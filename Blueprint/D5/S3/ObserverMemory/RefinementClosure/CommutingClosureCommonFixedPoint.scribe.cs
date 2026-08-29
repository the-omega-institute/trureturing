using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class CommutingClosureCommonFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two commuting closure operators compose to a closure whose fixed points are exactly their common fixed points.",
        H("Commuting Closure Common Fixed Point"),
        Blocks(
            Theorem(
                "commuting-composition-apply",
                "commutingComposition_apply",
                "Commuting Composition Apply",
                "This theorem establishes commuting composition apply in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "commuting-closure-composition-fixed-iff",
                "commuting_closure_composition_fixed_iff",
                "Commuting Closure Composition Fixed iff",
                "A point is fixed by the commuting composition exactly when it is fixed by both constituent closures.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "commuting-composition-order-independent",
                "commuting_composition_order_independent",
                "Commuting Composition Order Independent",
                "Commutativity makes the one-pass common closure independent of order.",
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
