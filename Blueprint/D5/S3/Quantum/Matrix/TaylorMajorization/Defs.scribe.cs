using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.TaylorMajorization;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/zhang2026weakmajorizationtaylor");

    private const string Module = "D5/S3/Quantum/Matrix/TaylorMajorization/Defs";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered Taylor coefficients and spectral comparison.",
        H("Taylor coefficients and weak majorization"), Blocks(
            Entry("taylor-majorization-q", "taylorQ", "Ordered Taylor coefficients",
                "Q at order k is the sum of choose(k,p) times A to the p times B to the k-p, for p from zero to k."),
            Entry("taylor-majorization-r", "taylorR", "Hermitian Taylor coefficients",
                "R at order k is the Hermitian part (Q+Q*)/2 of the ordered coefficient."),
            Entry("taylor-majorization-weakmaj", "weakMaj", "Spectral weak majorization",
                "Weak majorization compares all initial sums of the nonincreasing real eigenvalue lists. The empty sum at r=0 is an automatic equality; positive lengths up to the matrix dimension give the source comparison."),
            Entry("taylor-majorization-claim", "claim", "The unrestricted comparison",
                "For every positive dimension, every Hermitian A and B and every natural order k at least five, the eigenvalues of (A+B) to the k are weakly majorized by those of R at order k. No positivity assumption is imposed."),
            Describe.Lean(DescribeId.Create("taylor-majorization-defect"),
                DeclarationHandle.Create(Module + ".defect"),
                H("The real trace defect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The defect is the real trace of R minus the real trace of (A+B) to the k. A strictly negative defect contradicts the full spectral comparison."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("taylor-majorization-r-hermitian"),
                DeclarationHandle.Create(Module + ".taylorR_isHermitian"),
                H("Hermitian Taylor coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Hermitian part R is Hermitian at every order, so its sorted real eigenvalues are defined."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-trace-reduction"),
                DeclarationHandle.Create(Module + ".weakMaj_trace"),
                H("The full spectral sum is the trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Weak majorization of the nonincreasing real eigenvalues of Hermitian X and Y implies that the real trace of X is at most that of Y. Take the initial sum of length n and directly apply the existing RHLinalg real-trace identity and eigenvalue-sum reindexing theorem."))), DescribeRole.Theorem))));
    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
