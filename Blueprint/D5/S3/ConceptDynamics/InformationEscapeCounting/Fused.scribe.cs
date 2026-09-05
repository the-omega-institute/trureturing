using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeCounting;

internal sealed class FusedDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One saturated theorem-family scan classifies each ordered state pair.",
        H("Catalog-Wide Fused Counting"),
        Blocks(
            Def("state-enumeration", "StateEnumeration", "Complete state enumeration",
                "A duplicate-free list is certified to contain every arena state."),
            Def("index-enumeration", "IndexEnumeration", "Complete index enumeration",
                "A duplicate-free list is certified to contain every catalog index."),
            Def("finite-index-enumeration", "finIndexEnumeration",
                "Canonical finite-index enumeration",
                "The ascending finite range supplies a complete Fin n enumeration."),
            Def("fused-counts", "FusedCounts", "Catalog-wide result",
                "Full escape, unique counts, and fifteen role bins are accumulated together."),
            Def("fused-without", "without", "Derived leave-one-out count",
                "Leave-one-out escape is full plus the selected unique count."),
            Def("fused-zero", "zero", "Zero accumulator",
                "Every catalog-wide count starts at zero."),
            Def("mask-signature", "maskSignature", "Four-bit mask signature",
                "A Fin 16 mask is decoded in CUT, FLOW, ADMIT, ANCHOR order."),
            Def("bucket-mask", "bucketMask", "Nonzero bucket mask",
                "A Fin 15 bucket is shifted into the nonzero Fin 16 masks."),
            Def("bucket-of-mask", "bucketOfMask", "Mask bucket projection",
                "A nonzero mask is projected back to its zero-based bucket."),
            Def("role-signature-of-bucket", "roleSignatureOfBucket",
                "Bucket role signature",
                "Each bucket names one nonzero four-role signature."),
            Def("selected-mask", "selectedMask", "Selected theorem mask",
                "The four primitive-axis disagreements are packed into one mask."),
            Def("pair-scan", "PairScan", "Saturated disagreement class",
                "A pair has no disagreement, one indexed disagreement, or at least two."),
            Def("scan-after-one", "scanAfterOne", "Scan after first disagreement",
                "The remaining indices are inspected only until disagreement two."),
            Def("scan-indices", "scanIndices", "Single theorem-family scan",
                "Each pair traverses the catalog index enumeration at most once."),
            Def("catalog-pair-scan", "pairScan", "Certified catalog pair scan",
                "The saturated scan consumes a complete index enumeration."),
            Def("fused-bump", "bump", "Unique-bin increment",
                "One singleton disagreement increments its index and exact role bucket."),
            Def("pair-step", "pairStep", "One pair transition",
                "Off-diagonal pairs update exactly one classification branch."),
            Def("fused-counts-fold", "fusedCounts", "Strict fused census",
                "A strict nested fold classifies every ordered pair once."))));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);
}
