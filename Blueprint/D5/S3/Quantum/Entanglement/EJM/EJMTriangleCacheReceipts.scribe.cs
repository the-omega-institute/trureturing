using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTriangleCacheReceiptsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete kernel receipts for all triangle row mirrors and transitions.",
        H("Complete kernel receipts for all triangle row mirrors and transitions."),
        Blocks(
            Paragraph(Text("The kernel receipts exhaust all 41294 original rows, every unknown local coordinate, and all four possible outcomes. Equality remains equality of the complete original partial assignments. These local receipts do not assert complete global replay acceptance or nonlocality.")),
            Describe.Lean(DescribeId.Create("mirror-accepted"),
                DeclarationHandle.Create(Prefix + "mirror_accepted"),
                H("Every original mirror is accepted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All original assignment functions and all scaled lower fields satisfy the full original mirror predicate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transitions-accepted"),
                DeclarationHandle.Create(Prefix + "transitions_accepted"),
                H("Every complete original transition family is accepted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checker retains every unknown coordinate and every Fin 4 outcome."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("assignment-eq"),
                DeclarationHandle.Create(Prefix + "assignment_eq"),
                H("Each mirror assignment is the entire original row assignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This function equality exposes the original-row association used by the cache consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lower-eq"),
                DeclarationHandle.Create(Prefix + "lower_eq"),
                H("Every mirror lower equals the original scaled lower"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact original integer lower is retained without an external numerical premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transition-accepted"),
                DeclarationHandle.Create(Prefix + "transition_accepted"),
                H("Every original unknown-coordinate transition retains full assignment association"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem consumes original-row unknown status and earns acceptance of the generic exact transition checker."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create(Prefix + "accepted"),
                H("All local mirrors and transitions are jointly accepted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conjunction packages the two exhaustive kernel receipts for use by the full original replay consumer."))), DescribeRole.Theorem)))));
}
