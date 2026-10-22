using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.TaylorMajorization;

internal sealed class ShiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/TaylorMajorization/Shift";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar translation of Taylor defects.",
        H("Scalar translation of Taylor defects."), Blocks(
            Describe.Lean(DescribeId.Create("taylor-majorization-shift-taylorq-shift"),
                DeclarationHandle.Create(Module + ".taylorQ_shift"),
                H("Scalar translation of the ordered coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary complex square matrices A and B, a complex scalar s and every natural k, Q(A+sI,B) at order k is the sum over j from zero to k of choose(k,j) times s to the k-j times Q(A,B) at order j. Left multiplication by A and right multiplication by B commute as linear endomorphisms. The matrix coefficient is their binomial power applied to the identity, and translating A adds s times the identity endomorphism."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-shift-trace-taylorr"),
                DeclarationHandle.Create(Module + ".trace_taylorR"),
                H("Real trace of Hermitian symmetrization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any complex matrices A and B and any order k, the real traces of R and Q agree. Conjugate transpose conjugates the trace, and averaging a complex number with its conjugate preserves its real part."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-shift-defect-shift"),
                DeclarationHandle.Create(Module + ".defect_shift"),
                H("The binomial transform of the trace defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real scalar s, the defect at (A+sI,B) and order k is the sum over j from zero to k of choose(k,j) times s to the k-j times the defect at (A,B) and order j. Apply the ordered coefficient translation identity and the commuting binomial theorem for A+B and sI, then take real traces."))), DescribeRole.Theorem))));
}
