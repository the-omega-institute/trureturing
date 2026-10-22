using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class FiniteHermitianCharacterSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bilinear and self-paired binary graph modes have exact signed trace-character factors.",
        H("Finite Hermitian Character Sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-graph-character-sum"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/FiniteHermitianCharacterSum.paired_graph_character_sum"),
                H("The bilinear factor of independent opposite modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                        Paragraph(Text("Let K be any finite field of characteristic two, N any natural number, A a symmetric N by N binary matrix, and lambda_i nonzero elements of K. Define M_ij=A_ij(lambda_i+lambda_j). Define halfPhase(A,lambda,x,y) as the sum over i<j of A_ij(1+lambda_j/lambda_i)x_i y_j, with binary entries embedded into K. For every nontrivial complex additive character psi of K, the sum over independent x,y in K^N of psi(halfPhase(A,lambda,x,y)+halfPhase(A,lambda inverse,y,x)) equals |K|^(2N-rank M).")),
                        Paragraph(Text("Symmetry combines the two upper-triangular polynomials into (lambda inverse times x)-transpose M y. Row scaling is a bijection because every lambda_i is nonzero. For fixed y, character orthogonality gives zero unless M y=0, in which case the inner sum is |K|^N. The annihilator condition is proved by testing one coordinate against the nontrivial character. Rank-nullity gives |ker M|=|K|^(N-rank M). This includes N=0 and singular or zero matrices. No assertion of independent Fourier attainment is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("self-paired-trace-graph-sum"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/FiniteHermitianCharacterSum.self_paired_trace_graph_sum"),
                H("The positive trace factor of a self-paired graph mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                        Paragraph(Text("Let K be any finite characteristic-two field with a nonidentity involutive ring automorphism sigma, and let L be its actual fixed field. Let A and lambda be as above, with sigma(lambda_i)=lambda_i inverse. For any nontrivial complex additive character eta of ZMod 2, the sum over x in K^N of eta(Tr(K/ZMod 2)(halfPhase(A,lambda,x,sigma(x)))) equals |K|^(N-rank M)|L|^(rank M). The trace is the actual algebra trace. No trace nondegeneracy, Hermitian count, rank parity or sign is granted as a premise.")),
                        Paragraph(Text("The matrix B=diag(lambda inverse)M is Hermitian and has the same rank as M. The identity Tr(K/L)(halfPhase)=x-transpose B sigma(x) follows by pairing the upper and lower triangles. The trace tower transports this identity to the prime-field character, whose nontriviality follows from the finite-field trace character theorem.")),
                        Paragraph(Text("Finite Hermitian congruence gives an identity block of size rank B and a zero radical. An invertible change of vector coordinates leaves the sum unchanged. Each radical coordinate contributes |K|. Each norm coordinate contributes -|L|: the norm is onto on units, each nonzero fibre has |L|+1 elements, and the sum of a nontrivial additive character on L is zero. Thus the signed general Hermitian sum is |K|^(N-rank B)(-|L|)^(rank B).")),
                        Paragraph(Text("The binary source matrix M is symmetric with zero diagonal and hence alternating. Restrict its bilinear form to a complement of the radical, prove nondegeneracy there, and use a symplectic basis to see that its rank is even. This removes the negative sign. Singular forms and N=0 retain their radical factors. This is a local mode count; a global Fourier decomposition and its multiplicities are separate requirements."))),
                DescribeRole.Theorem))));
}
