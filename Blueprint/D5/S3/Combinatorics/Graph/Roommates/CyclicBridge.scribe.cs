using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class CyclicBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial components of the Mertens range-two proof; the full theorem remains open.",
        H("CyclicBridge"), Blocks(
            Describe.Lean(DescribeId.Create("closing-request-source-target"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_request_source_target"),
                H("closing_request_source_target"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual buffer target of every closing request is the original signed-offset neighbor in the literal source cycle of size m+6. Both left and right exterior requests preserve their cyclic destinations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closing-old-edge-local"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_edge_local"),
                H("closing_old_edge_local"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A six-site closing buffer creates no wrap edge between old vertices. Every source edge with two old endpoints has integer separation at most two, including old lengths one and two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed"),
                H("signed"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four supplier labels represent signed offsets 1,2,-1,-2 in that order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wrap"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap"),
                H("wrap"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer coordinates are reduced modulo N=n+5; all four neighbors remain distinct, including N=5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("displacement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.displacement"),
                H("displacement"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed point is a single with displacement zero. An acceptable matched vertex retains its unique signed source offset when the cycle is cut."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cut-certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut_certificate"),
                H("cut_certificate"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cut every acceptable stable partial matching to a certificate on the unchanged ranking word. Reciprocity holds for integer targets that remain inside. Target injectivity includes exterior targets, by reduction to the injective cyclic partner permutation. Internal stability uses exact rank correspondence and strict rank injectivity; singles retain rank four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut"),
                H("cut"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map preserves the ranking word exactly and changes only the existential proof. It counts profiles once, independently of the number of stable matching witnesses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-count-le-open-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_count_le_open_count"),
                H("source_count_le_open_count"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n>=0, hence every cycle size N=n+5>=5, the number of successful source profiles is at most the number of certified words of length N. There is no parity restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-probability-eq"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_eq"),
                H("source_probability_eq"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of N independent uniform neighbor rankings has 24 choices. The literal supplier probability is the number of successful profiles divided by 24^N."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-probability-le-open-proportion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_le_open_proportion"),
                H("source_probability_le_open_proportion"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic cut gives the upper comparison p_N<=b_N/24^N. The inverse closure injection, padded supermultiplicativity and exact same-q theorem remain unproved here."))), DescribeRole.Theorem))));
}
