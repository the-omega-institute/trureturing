using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PointwiseTensorGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit tensor geometry of a finite matrix-unit representation with a positive commutant weight.",
        H("PointwiseTensorGeometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("matrix-unit-pointwise-tensor"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/PointwiseTensorGeometry.matrix_unit_pointwise_tensor"),
            H("matrix unit pointwise tensor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
            Blocks(
                Paragraph(Text("The constructed inverse endomorphism satisfies sigmaInv(w) = Rw as an ambient Euclidean vector. This exposes the restriction formula already used in the pointwise construction and is consumed by the global smooth inverse map.")),
                Paragraph(Text("The inputs are complex linear maps F(i,j) on C^n satisfying F(i,j) F(k,l) = delta(j,k) F(i,l), F(i,j)* = F(j,i), sum_i F(i,i) = P, and P F(i,j) = F(i,j). The ambient matrix P is a self-adjoint idempotent. Q is positive semidefinite and commutes with the F(i,j). An ambient R satisfies QR = RQ = P and preserves range(F(v,v)). The trace premise is trace(Q F(v,v)) = 1. Finally NX(T) = Q sum_ij T(i,j) F(i,j) for every complex T.")),
                Paragraph(Text("Set E0 = range(P) and K0 = range(F(v,v)), with the inherited complex inner products. The constructed maps are col_i(w) = F(i,v)w, B(y)_i = F(v,i)y, and S(f) = sum_i col_i(f_i). Matrix-unit multiplication proves BS = identity and SB = identity on E0. The standard tensor coordinate equivalence C: K0 tensor C^d -> (d -> K0) sends w tensor e_i to the function supported at i with value w. Theta is S composed with C, and its inverse is x -> sum_i B(x)_i tensor e_i.")),
                Paragraph(Text("The canonical tensor metric is established rather than assumed: the adjoint and matrix-unit laws give inner(col_i(w),col_j(u)) = delta(i,j) inner(w,u). Expanding both tensors in the standard basis then gives inner(Theta(z),Theta(zprime)) = inner(z,zprime). Thus Theta is an isometric linear equivalence. The adjoint of Theta equals its inverse. The inherited subspace inclusions jE and jK satisfy jE* jE = identity, jE jE* = P, jK* jK = identity, and jK jK* = F(v,v).")),
                Paragraph(Text("The multiplicity operator sigma is the actual restriction of Q to K0; sigmaInv is the restriction of R. Commutation makes the restrictions well defined, and QR = RQ = P proves both inverse identities. Positivity descends from Q. If the quadratic form vanishes, the positive-semidefinite zero-form criterion gives Qw = 0, and the inverse identity forces w = 0. Therefore the quadratic form is strictly positive on each nonzero w.")),
                Paragraph(Text("Trace cyclicity identifies trace(sigma) with trace(Q F(v,v)), hence with one. Matrix-unit commutation proves Q Theta(z) = Theta((sigma tensor identity)z). With U = jE Theta, the explicit inverse coordinates and the complex matrix-unit expansion prove NX(T) = U (sigma tensor T) U* for every complex matrix T.")),
                Paragraph(Text("This is a repository-derived construction with explicit range coordinates, built from Mathlib tensor coordinates, tensor inner products, adjoints, positivity and trace cyclicity. The finite fixed-ancilla normal form is classical prior literature (Nayak and Sen, Theorem 2.1); no external novelty is claimed. This theorem assumes the matrix-unit and spectral relations. The PointwiseTensorRecovery consumer derives those premises from the actual Kraus channel and left inverse. No global smooth bundle, frame, topology or control statement is proved here."))),
            DescribeRole.Theorem))));
}
