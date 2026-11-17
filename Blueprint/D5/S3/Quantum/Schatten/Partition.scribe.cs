using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class PartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sra's finite Schatten partition inequality via the existing Carlen-Lieb theorem.",
        H("The full Schatten partition inequality"), Blocks(
            Describe.Lean(DescribeId.Create("trace-root-subadditivity"),
                DeclarationHandle.Create("D5/S3/Quantum/Schatten/Partition.rootTrace_sum"),
                H("PSD trace-root subadditivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/sra2026partition")),
                Blocks(Paragraph(Text("For every real q in [1,2], every finite PSD family A_j and every PSD square Z, Re Tr((Z* (sum_j A_j)^q Z)^(1/q)) is at most the sum of the individual traces Re Tr((Z* A_j^q Z)^(1/q)). The power 1/q is a spectral matrix power inside the trace. The existing fixed-congruence Carlen-Lieb convexity theorem is reused. CFC scalar homogeneity converts convexity into subadditivity for positive definite arguments. Regularizing each input and Z by epsilon I, then applying genuine positive-power continuity, proves the singular case. Finite induction includes an empty family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rectangular-power"),
                DeclarationHandle.Create("D5/S3/Quantum/Schatten/Partition.rectangularNorm_rpow"),
                H("The actual rectangular Schatten power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/sra2026partition")),
                Blocks(Paragraph(Text("For every positive real p and every finite rectangular complex matrix X, rectangularNorm X p raised to p equals the real trace of (XX*)^(p/2). This is the existing proof, exposed without changing its hypotheses or body so that the Peled rank-one compound consumer can reuse it. Empty dimensions and zero singular values remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rectangular-partition"),
                DeclarationHandle.Create("D5/S3/Quantum/Schatten/Partition.partition_rectangular"),
                H("Every compatible rectangular complex matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/sra2026partition")),
                Blocks(Paragraph(Text("For arbitrary finite types indexing the PSD summands, rows and columns, every real 1<=p<=2 and every compatible complex X, with H=sum_j H_j positive definite, the sum of the pth powers of the Schatten p norms of H_j^(1/p) H^(-1/p) X is at least the pth power of the Schatten p norm of X. Singular H_j and singular or zero X are retained. The rectangular Schatten functional is defined using the existing actual schattenNorm of sqrt(XX*); its pth power is proved to equal the real trace of (XX*)^(p/2). It agrees with the existing square Schatten functional.")),
                    Paragraph(Text("Set K=H^(-1/p), M=K XX* K, Z=sqrt(M) and q=2/p. Apply PSD trace-root subadditivity at q. The existing equality between the Schatten Gram and row-Gram traces swaps the two square factors and identifies every summand with the actual rectangular Schatten pth power. At H, the genuine CFC inverse powers cancel to give XX*. No interpolation hypothesis, desired row bound, commuting surrogate or operator-valued concavity is assumed.")),
                    Paragraph(Text("Empty row or column dimensions give a zero row Gram trace, so both sides are zero. An empty partition has H=0 and can satisfy positive definiteness only in empty row dimension; the finite-sum base case and the same zero trace computation cover it. No nonempty index or dimension premise is added, and no operator norm is asserted to equal one in a zero space."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("square-partition"),
                DeclarationHandle.Create("D5/S3/Quantum/Schatten/Partition.partition"),
                H("The existing actual Schatten functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/sra2026partition")),
                Blocks(Paragraph(Text("This is Theorem 1.2 in the existing schattenNorm notation, using the proved rectangular-to-square equality. All real exponents from one to two, arbitrary finite complex PSD partitions with SPD sum, and every square complex free matrix are included. This is a formalization of Sra's published theorem, with an alternative proof through the already formalized Carlen-Lieb convexity. It is an analytic supplier for the unchanged Audenaert/common-Z/three-point program and does not complete that original research goal. No original/unique KPI is claimed."))),
                DescribeRole.Theorem))));
}
