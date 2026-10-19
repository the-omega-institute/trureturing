using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTriangleCacheReceiptsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete triangle mirror and transition kernel receipts",
        H("Complete triangle mirror and transition kernel receipts"),
        Blocks(
            Paragraph(Text("The finite proof blocks form 22 imported interval groups. The complete mirror and transition receipts consume every group by exhaustive interval dispatch.")),
            Paragraph(Text("The interval-dispatched receipts cover every one of the 41294 rows. The transition guard restricts verification to the original unknown coordinates and preserves all 342224 actual value transitions. The cache association theorem applies these receipts only after proving that the actual coordinate is unknown. No external generator check, producer premise, partial sample or native evaluator is an acceptance theorem.")),
            Node("mirror-accepted", "mirror_accepted", "Every original row has an exact mirror",
                "All finite chunks of the mirror check are consumed by exhaustive index dispatch. The receipt supplies the whole assignment equality and exact lower equality.", DescribeRole.Theorem),
            Node("transitions-accepted", "transitions_accepted", "Every actual unknown-coordinate/value transition is exact",
                "Exhaustive row dispatch supplies each complete transition checker result. All four values and every unknown coordinate remain quantified in the checked proposition.", DescribeRole.Theorem),
            Node("assignment-eq", "assignment_eq", "Mirror assignments are the original assignments",
                "This extracts the assignment component of the full mirror receipt at an arbitrary actual row index.", DescribeRole.Theorem),
            Node("lower-eq", "lower_eq", "Literal lower fields equal original scaled bounds",
                "This extracts exact integer equality from the mirror receipt, permitting later leaf arithmetic to reuse small literals without changing the bound.", DescribeRole.Theorem),
            Node("transition-accepted", "transition_accepted", "Earn the generic cache transition on original rows",
                "The actual unknown-coordinate hypothesis and full mirrored transition receipt are rewritten through both assignment equalities. The result is the generic checkTransition theorem for the original row function.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
