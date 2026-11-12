using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class OpenCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable partial matchings and the Mertens range-two probability estimate.",
        H("OpenCertificates"), Blocks(
            Describe.Lean(DescribeId.Create("rank-injective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.rank_injective"),
                H("rank_injective"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a ranking permutation and nonzero integer offsets a and b between -2 and 2, equality of offsetRank implies a=b. The paired-certificate construction uses this injectivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("offsetrank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.offsetRank"),
                H("offsetRank"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.Certificate"),
                H("Certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certifiedword"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.CertifiedWord"),
                H("CertifiedWord"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count"),
                H("count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate-restrict"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.certificate_restrict"),
                H("certificate_restrict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-submultiplicative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_submultiplicative"),
                H("count_submultiplicative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-lower"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_lower"),
                H("count_lower"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exclusivetriangle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.ExclusiveTriangle"),
                H("ExclusiveTriangle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exclusive-triangle-not-certified"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified"),
                H("exclusive_triangle_not_certified"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. PaddedCompletion supplies concatenation; CyclicBridge and CyclicClosure supply the cyclic comparisons; TriangleCount supplies the strict count, and GrowthTransfer.result is their common-base probability consumer."))), DescribeRole.Theorem))));
}
