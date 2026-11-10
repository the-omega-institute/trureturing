using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class ElementaryGaussianContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native Gaussian contraction with zero shared diagonal",
        H("Elementary factorial Gaussian contraction"),
        Blocks(
            Paragraph(Text("Let I, J and E be arbitrary finite mode types, including empty types. The external occupations d and e and shared occupation n are finitely supported natural families. P on I and Q on E are arbitrary complex symmetric matrices. R from I to J and S from J to E are arbitrary complex matrices. All products are bilinear; transpose has no complex conjugation.")),
            Paragraph(Text("The factorial normalization is classical symmetric/Bargmann Fock normalization, and the Gaussian pairing is classical Wick calculus. No literature novelty or exact external theorem attribution is claimed. AssessedProvenance.FromRepo records reuse of FactorialFockMetric and FactorialFockQuadraticEstimate, together with the unchanged nativeMoment and nativeMoment_step suppliers in NativeGaussianMoment. The retained inference is the native finite contraction, with a proved support bound and exact factorial reindexing.")),
            D("leftKernel", "First block kernel", "The blocks are P, R, transpose(R), and zero on J. Its shared diagonal vanishes."),
            D("rightKernel", "Second block kernel", "The blocks are zero on J, S, transpose(S), and Q. Its shared diagonal vanishes."),
            D("effectiveKernel", "Bilinear effective kernel", "The blocks are P, R S, transpose(R S), and Q. Matrix multiplication sums exactly over the finite shared mode type."),
            N("coefficient_contraction", "Native finite coefficient identity", "Sum weight(n) times gaussianCoefficient(leftKernel, d.sumElim(n)) times gaussianCoefficient(rightKernel, n.sumElim(e)) over all n of degree at most min(degree(d),degree(e)). The sum is exactly gaussianCoefficient(effectiveKernel,d.sumElim(e)). The weight is the existing FactorialFockMetric.weight, the product of occupation factorials."),
            Paragraph(Text("The proof directly reuses NativeGaussianMoment.nativeMoment and nativeMoment_step. Shared insertion has no shared/shared contribution, so each shared occurrence consumes an external occurrence. Induction proves vanishing when shared degree exceeds external degree on either side. Bounded-degree occupations form a finite set. In the contraction recurrence, n_a/weight(n) is reindexed by n=m+e_a and becomes 1/weight(m), using weight(m+e_a)=(m_a+1)weight(m). The second shared insertion supplies the cross block R S. A boundary comparison and induction on the first external degree identify the contracted moments with the effective native moment. External factorials cancel, leaving the ordinary coefficient identity.")),
            Paragraph(Text("There is no convergence or positivity hypothesis. The vacuum scalar is one. This proves no nontrivial determinant sewing invariant. Nonzero shared squeezing, countable limits, full corrected-field coefficients, Gram transformation, physical unitarity, VOA/CFT axioms, fusion, anomalies, string dynamics and AdS/CFT remain outside the result."))),
        []));

    private static DocumentBlock D(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("elementary-gaussian-contraction-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("elementary-gaussian-contraction-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
