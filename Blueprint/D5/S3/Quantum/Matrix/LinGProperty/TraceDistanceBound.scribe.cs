using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class TraceDistanceBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive block overlap controls the squared difference of trace-one diagonal blocks.",
        H("The diagonal difference bound"), Blocks(
            Describe.Lean(DescribeId.Create("normalized-trace-norm-le-one"),
                DeclarationHandle.Create(Owner + "normalized_trace_norm_le_one"),
                H("The normalized overlap is at most one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("Summing the coordinate block compressions gives a positive two-by-two matrix with diagonal entries one and off-diagonal entry tr X. Its positive semidefinite entry bound gives |tr X| squared at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-difference-square-le"),
                DeclarationHandle.Create(Owner + "normalized_difference_square_le"),
                H("A squared Loewner bound from the block overlap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(
                    Paragraph(Text("Let W=[A X; X-adjoint B] be positive semidefinite, with tr A=tr B=1. Then (A-B) squared is bounded above by (1-|tr X| squared) times the identity in the Loewner order. All finite dimensions and singular diagonal blocks are included.")),
                    Paragraph(Text("For any set of coordinates, sum its two-by-two principal block compressions. The positive semidefinite entry inequality bounds the squared modulus of its X-diagonal sum by the product of the corresponding A and B masses. Apply this to one coordinate and its complement. The triangle inequality gives |tr X| no greater than sqrt(ab)+sqrt((1-a)(1-b)).")),
                    Paragraph(Text("The finite total-variation and affinity inequality, applied to the two probability vectors (a,1-a) and (b,1-b), bounds (a-b) squared by one minus the squared affinity. Conjugate all three blocks by the same eigenbasis of A-B. The coordinate bounds then apply to every eigenvalue of that difference, and conjugating back gives the stated squared matrix bound."))),
                DescribeRole.Theorem))));
}
