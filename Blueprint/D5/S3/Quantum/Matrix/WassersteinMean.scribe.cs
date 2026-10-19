using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class WassersteinMeanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/WassersteinMean";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/gankim2024wasserstein");
    private const string Locator = "arXiv:2301.07934v4, §5, Conjecture 5.7";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The geometric and Wasserstein matrix means, their real power transform, "
        + "and weak log-majorization through decreasingly sorted eigenvalue products.",
        H("Wasserstein power means and eigenvalue products"),
        Blocks(
            Paragraph(Text(Locator + ".")),
            Paragraph(Text("A ⋄t B := (1 − t)² A + t² B + t(1 − t)[A(A^{−1} #B) + (A^{−1} #B)A]")),
            Paragraph(Text("Conjecture 5.7. Let A, B ∈ Pm and t ∈ (0, 1). Then "
                + "(A^p ⋄t B^p)^{1/p} ց≺w log exp((1 − t) log A + t log B) as p ց 0.")),
            Describe.Lean(
                DescribeId.Create("wasserstein-mean"),
                DeclarationHandle.Create(Module + ".wassersteinMean"),
                H("The weighted Wasserstein mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The mean is exactly the displayed polynomial expression "
                    + "in A, B and A⁻¹ # B, with real weight t. The geometric mean reuses the "
                    + "base-first weighted mean in PsiMeanTraceConcavity at weight 1/2, using "
                    + "CFC.rpow. For positive definite inputs and "
                    + "0≤t≤1 it also equals ((1−t)I+tT) A ((1−t)I+tT), where T=A⁻¹ # B "
                    + "is the positive definite solution of TAT=B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wasserstein-power-mean"),
                DeclarationHandle.Create(Module + ".powerMean"),
                H("The power-transformed Wasserstein mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("F A B t p is (A^p ⋄t B^p)^(1/p), with both the input "
                    + "powers and the outer reciprocal power interpreted by the real continuous "
                    + "functional calculus via SpectralPower.mpow. "
                    + "The proposed limit uses that module’s LE t A B, namely "
                    + "exp((1−t) log A+t log B). This is the expression in Conjecture 5.7."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wasserstein-weak-log-majorization"),
                DeclarationHandle.Create(Module + ".weakLogMajorization"),
                H("Weak log-majorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Hermitian witnesses supply real eigenvalues sorted in "
                    + "decreasing order. For each prefix length k up to the dimension, the product "
                    + "of the first k eigenvalues of X is at most the corresponding product for Y. "
                    + "The empty prefix is harmless; the full prefix is essential. For the positive "
                    + "definite matrices in the conjecture, all eigenvalues are positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wasserstein-weak-log-majorization-determinant"),
                DeclarationHandle.Create(Module + ".weakLogMajorization_det_le"),
                H("The full prefix compares determinants"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The prefix containing every eigenvalue gives det X≤det Y "
                    + "for the real determinants of Hermitian matrices. The determinant equals the "
                    + "product of the eigenvalues, and sorting only permutes the factors. "
                    + "This implication detects the determinant obstruction in the counterexample."))),
                DescribeRole.Theorem))));
}
