using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class OpenCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial formal development of the exact Mertens range-two problem; the full theorem remains open.",
        H("OpenCertificates"), Blocks(
            Describe.Lean(DescribeId.Create("offsetrank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.offsetRank"),
                H("offsetRank"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.Certificate"),
                H("Certificate"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certifiedword"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.CertifiedWord"),
                H("CertifiedWord"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count"),
                H("count"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate-restrict"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.certificate_restrict"),
                H("certificate_restrict"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-submultiplicative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_submultiplicative"),
                H("count_submultiplicative"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-lower"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.count_lower"),
                H("count_lower"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exclusivetriangle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.ExclusiveTriangle"),
                H("ExclusiveTriangle"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exclusive-triangle-not-certified"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/OpenCertificates.exclusive_triangle_not_certified"),
                H("exclusive_triangle_not_certified"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Open certificates retain the ranks of exterior requests and injectivity of all integer targets. Restricting an interval preserves reciprocity and internal nonblocking. Splitting is injective on ranking words, not on chosen certificates. The lower bound pairs successive sites and permits the last odd site to request an exterior partner. The directed exclusive triangle cannot be certified even with exterior partners or singles. General concatenation, cyclic cut and closure, exact obstruction cardinality, and the full source-model theorem remain unresolved."))), DescribeRole.Theorem))));
}
