using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class ActualGraphLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-square-grid nonvanishing from typed complex neighborhoods.",
        H("ActualGraphLift"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-decode"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.decode"),
                H("decode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Specialize the existing analytic inverse to the actual coefficient owner. This exposes its value without naming the analytic module's private accessors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-neutral-message"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.neutralMessage"),
                H("neutralMessage"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact coordinate of a missing child, whose vacancy is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-neutral-message-neutral-message-2"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.neutral_message"),
                H("neutral message"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every type has a genuine neutral message inside its open neighborhood."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-complex-child-absent"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.complex_child_absent"),
                H("complex child absent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A missing nonroot direction has complex vacancy one once only the proper pre-recentered partitions are known nonzero. Real positivity is not used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-complex-root-child-absent"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.complex_root_child_absent"),
                H("complex root child absent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The missing fourth-root factors also have value one using only smaller pre-recentered domains. No nonzero root partition is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-actual-pruning"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.actual_pruning"),
                H("actual pruning"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual vertex-membership pruning is legal in the existing finite geometric presentation. Its successor type and smaller domain are derived."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-decoded-child-product"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.decoded_child_product"),
                H("decoded child product"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Algebraically identify the represented child product with the complete actual graph product, inserting only the rigorously proved neutral factors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-typed-graph-step"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.typed_graph_step"),
                H("typed graph step"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One genuine internal graph step consumes smaller-domain nonvanishing and actual child representations. It derives the parent nonvanishing and its message representation, without assuming either parent conclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-final-actualgraphlift-root-graph-step"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/ActualGraphLift.root_graph_step"),
                H("root graph step"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reconstruct the unconditioned root from actual type-zero child messages. The half-plane bound is retained for a quantitative partition lower bound."))), DescribeRole.Theorem))));
}
