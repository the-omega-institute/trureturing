using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeTwoCurrentTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two neutral currents on complete finite energy grades.",
        H("Finite Two-Current Trace"),
        Blocks(
            Definition("current-block", "actualCurrentBlock", "Original current grade block",
                "For every lattice D, current index i and natural grades n,m, the block from grade m to grade n is the original Y(currentState i) coefficient m-n, followed by the original grade-n projection. Its domain and codomain are the original full charge and ordinary monomial grades."),
            Definition("current-cycle-trace", "actualCurrentCycleTrace", "Finite actual cycle trace",
                "Assuming the real integral Gram matrix is positive definite, the n-th full grade is finite dimensional. The cycle trace is the complex linear-map trace of B_i(n,m) composed with B_j(m,n) on that grade. No trace on the infinite carrier is taken."),
            Definition("ordinary-multiplicity", "occupationMultiplicity", "Ordinary oscillator multiplicity",
                "The multiplicity p_D(a) is the natural cardinality of the original IntegerFiber D a, cast to the complex numbers. Every ordinary oscillator monomial has weight one."),
            Theorem("two-current-grade-trace", "actual_two_current_grade_trace", "Exact finite two-current trace",
                "For every positive-definite even integral Gram matrix D, every pair i,j of current indices and all natural grades n,m, put Q(beta)=chargeEnergy(beta).toNat and h_i(beta)=bilinear(unitCharge i,beta). If n=m, the actual cycle trace is the sum over positiveChargeCutoff D hD n of h_i(beta) h_j(beta) p_D(n-Q(beta)). If n differs from m, put ell=Nat.dist n m and a=min(n,m)-Q(beta). The trace is ell times G(i,j) times the sum over positiveChargeCutoff D hD min(n,m), and over k from zero through a/ell inclusive, of p_D(a-k ell). All integer and natural coefficients are cast faithfully to the complex numbers; the Gram and charge cross terms retain their signs."),
            Paragraph(Text("At positive frequency ell, the original creation action multiplies by X(j,ell-1), and the returning annihilator has diagonal coefficient ell G(i,j) times the occupation of that variable plus one. The finite bijection deleting k marked particles identifies pairs (w,k) with k at most w(j,ell-1) with residual occupations of energy a-k ell. Its inverse adds those particles back. This establishes the marked count used in the trace sum. The opposite grade ordering follows from finite rectangular trace cyclicity and Gram symmetry. Equal grades use the original charge zero modes.")),
            Paragraph(Text("The charge cutoff contains every charge in the complete lower grade by positivity. No inverse Gram, determinant-unit, factorial pairing or convergence premise is used. Zero grades and all finite ranks are included; at rank zero there are no current indices. This finite identity makes no analytic, modular or sewing assertion.")))));
    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
