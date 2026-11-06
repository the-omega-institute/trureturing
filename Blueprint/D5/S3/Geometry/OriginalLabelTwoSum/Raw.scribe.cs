// UNCOMPILED Scribe preparation. No native emit, catalog resolution, rendered
// fidelity, source selection or registration/audit receipt has been observed.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class RawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Raw.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/Raw"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/Raw"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-two-sum-source")),
            [], Digest.Create("Original-label Gamma/two-filling source preparation; native verification remains open.")),
        H("Raw"),
        Blocks(
            Node("family", "Family", "Family",
                "Actual source declaration; elaboration, native selection and audits remain OPEN.", DescribeRole.Definition),
            Node("supported", "Supported", "Supported",
                "Ground support includes every face, including the empty face when present. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("delta", "delta", "delta",
                "The raw simplex on the given original labels. In particular delta empty is UNIT. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("rows", "Rows", "Rows",
                "Original rows are indexed, even when two rows have identical complements. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("rows-root", "root", "root",
                "No row means VOID; an empty complement of an existing row contributes UNIT. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("without", "without", "without",
                "Row deletion is restriction of the index type, and does not delete a vertex. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("restrict", "restrict", "restrict",
                "Literal simplicial deletion on the specified surviving ground. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("rawlink", "rawLink", "rawLink",
                "Link preserves absence of the raw empty face. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("rawjoin", "rawJoin", "rawJoin",
                "Augmented join on the same original ambient type; support/disjointness is proved by consumers. It does not silently supply an empty factor. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("project", "project", "project",
                "Projection discards just the empty face, after all raw operations. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("nativeaug", "nativeAug", "nativeAug",
                "Reuse the native owner's augmentation ONLY when a raw-empty witness is available at the call site. It is not an inverse projection on VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("project-nativeaug", "project_nativeAug", "project_nativeAug",
                "Reuse the native owner's augmentation ONLY when a raw-empty witness is available at the call site. It is not an inverse projection on VOID. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("reconstruct-nonvoid", "reconstruct_nonvoid", "reconstruct_nonvoid",
                "This reconstruction REQUIRES raw empty membership, rather than identifying VOID with UNIT through their common nonempty projection. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("raw-ext", "raw_ext", "raw_ext",
                "The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("mem-delta", "mem_delta", "mem_delta",
                "The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("mem-project", "mem_project", "mem_project",
                "The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("root", "Root", "Root",
                "The full original ground is independent of which singleton faces occur. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("asroot", "asRoot", "asRoot",
                "The full original ground is independent of which singleton faces occur. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("phi", "phi", "phi",
                "The exact parent formula; R is never a fake coordinate e. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("root-supported", "root_supported", "root_supported",
                "Complement roots are supported even when their row family is empty. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("rawjoin-void", "rawJoin_void", "rawJoin_void",
                "Complement roots are supported even when their row family is empty. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("rawjoin-unit", "rawJoin_unit", "rawJoin_unit",
                "Complement roots are supported even when their row family is empty. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("join-split", "join_split", "join_split",
                "Split coordinates are unique on disjoint original grounds. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem),
            Node("substitute", "substitute", "substitute",
                "Every original row is retained in this literal substitution. This is raw presentation transport, not a claimed graph unique-path substitution theorem. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("transportedrows", "transportedRows", "transportedRows",
                "Indexed complementary rows after replacement, on the actual new ground. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Definition),
            Node("row-transport", "row_transport", "row_transport",
                "Literal transport membership. The proof keeps the original chord indices; redundant rows and UNIT-producing complements are not discarded. Source-only draft; elaboration and native binding are OPEN.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
