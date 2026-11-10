using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteCriticalCellSphere;
internal sealed class AttachmentCollarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar",
            "The attachment collar and core quotient.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("The attachment collar and core quotient"),
        Blocks(Paragraph(Text("The input retains the original ambient labels, a nonempty attached face, the exact union with its simplex and full-boundary intersection, and only a standalone based contraction of the core. Closed radial and attachment pasting constructs the collar, its endpoint quotient inverse and both homotopies fixing the retained basepoint.")),
            Describe.Lean(DescribeId.Create("diskrestrict"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict"),
                H("diskRestrict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restrict an actual disk-set point to its original simplex coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("diskin-restrict"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict"),
                H("diskIn_restrict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inclusion after restriction is the original actual attachment point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("restrict-diskin"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn"),
                H("restrict_diskIn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restriction after disk inclusion is the original simplex point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cover"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover"),
                H("cover"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual attachment point is in the core or its attached simplex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("core-closed"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed"),
                H("core_closed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The included original core is closed in the attachment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("disk-closed"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed"),
                H("disk_closed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The attached original simplex is closed in the attachment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("diskin-mem-core-iff"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff"),
                H("diskIn_mem_core_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Disk inclusion is in the core exactly on the full simplex boundary."))), DescribeRole.Theorem))));
}
