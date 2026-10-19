using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CayleyResolventDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CayleyResolvent";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/czerwinska2026radial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cayley transport and endpoint resolvent bounds on the Hermitian matrix interval.",
        H("Cayley transforms and resolvent increments"), Blocks(
        Item("resolvent", "Real-parameter resolvent",
            "For a real scalar s and a finite complex square matrix A, define R_s(A)=(sI−A) inverse. "
            + "The definition uses Mathlib's nonsingular inverse; the endpoint theorem requires positive definite denominators.", true),
        Item("inverse_antitone", "Inverse reverses positive order",
            "For every dimension and positive definite complex matrices P,Q with P≤Q, one has Q inverse≤P inverse. "
            + "The comparison is the existing inverse antitonicity theorem on the strictly positive cone."),
        Item("endpoint_resolvent_factors", "Uniform endpoint factors",
            "For every dimension, let s≥2, U≤V, and suppose I+U, I−U and I−V are positive definite. Put H=V−U. "
            + "There is Z_U with R_s(V)−R_s(U)=R_s(U) Z_U R_s(U) and H≤Z_U≤3H. "
            + "There is Z_V with R_s(V)−R_s(U)=R_s(V) Z_V R_s(V) and H/3≤Z_V≤H. "
            + "The factors may differ. The first is H+H R_s(V) H. The second is "
            + "H^(1/2)(I+H^(1/2) R_s(V) H^(1/2)) inverse H^(1/2). "
            + "Mathlib's Woodbury identity establishes the second factorization without assuming H invertible. "
            + "Both bounds use positive matrix order and include singular increments."),
        Item("cayley", "Cayley map",
            "Define h(A)=I−2(A+I) inverse on finite complex square matrices. "
            + "On positive definite matrices this is the usual matrix Cayley transform associated with (t−1)/(t+1).", true),
        Item("cayley_transport", "Order-preserving Cayley transport",
            "For every positive definite A, both I+h(A) and I−h(A) are positive definite. "
            + "For every positive definite B with A≤B, one has h(A)≤h(B). "
            + "The proof reuses Mathlib's inverse order inequality. Positivity of I+h(A) follows "
            + "from the commuting positive definite product A(A+I) inverse."),
        Item("cayley_resolvent", "Resolvent of a Cayley image",
            "For every positive definite A and every real s≥2, "
            + "R_s(h(A))=(A+I)((s−1)A+(s+1)I) inverse. "
            + "Both denominator matrices are positive definite. Exact multiplication establishes "
            + "the inverse identity. The parameters s=2,3,4 give the three rational summands "
            + "used by the Czerwińska–Franco–Merino counterexample."))));

    private static DocumentBlock Item(string name, string title, string explanation, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(),
            definition ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
