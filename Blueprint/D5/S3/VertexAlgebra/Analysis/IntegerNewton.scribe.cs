using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class IntegerNewtonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Newton reconstruction and diagonal contact coefficients",
        H("Integer Newton reconstruction and diagonal contact coefficients"),
        Blocks(
            Paragraph(Text("Mathlib supplies completion, normed operators, Fourier analysis, integer binomial identities and unconditional sum machinery under Apache 2.0. The additional arguments here concern the stated original objects and relations. No literature novelty or physical realization is asserted.")),
            Describe.Lean(DescribeId.Create("integernewton-int-newton-of-fwdDiff-iter-eq-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero"),
                H("Two-sided Newton reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any additive commutative group V, sequence q:Z->V, and natural N with its Nth forward difference zero, every integer m satisfies q(m)=sum over 0<=j<N of choose(m,j) acting on the jth difference at zero. The binomial coefficient is the integer binomial, including negative m. At N=0 the hypothesis makes q identically zero and the sum is empty. The proof integrates the difference by Pascal recursion and uses induction in both directions on the integers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integernewton-delta-newton"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/IntegerNewton.delta_newton"),
                H("Reconstruction along every diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For C:Z->Z->V killed by delta^N, delta C(m,n)=C(m+1,n)-C(m,n+1), each C(m,n) is sum over j<N of choose(m,j) times c_j(m+n). Here c_j(t)=sum over i<=j of (-1)^(j-i)*choose(j,i) acting on C(i,t-i). The diagonal forward difference agrees with the corresponding delta iterate after its exact index shift. No mode is restricted to nonnegative integers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integernewton-choose-succ-mul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/IntegerNewton.choose_succ_mul"),
                H("Descending-factorial recursion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Over every characteristic-zero field, (j+1)*choose(x,j+1)=(x-j)*choose(x,j) for each x and natural j. Mathlib supplies the descending-factorial identity; cancellation of the nonzero factorial yields this recurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integernewton-norm-int-choose-le-pow"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/IntegerNewton.norm_int_choose_le_pow"),
                H("Polynomial bound for integer binomials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every integer m and natural j, the complex norm of the integer choose(m,j) is at most (1+abs(m))^j. The induction uses the descending-factorial recurrence and the inequality abs(m-j)<=(1+abs(m))*(j+1), so the estimate also covers negative m and j=0."))), DescribeRole.Theorem)),
        []));
}
