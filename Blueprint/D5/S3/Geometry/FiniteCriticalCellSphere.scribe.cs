using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteCriticalCellSphereDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteCriticalCellSphere",
            "Public import facade for the substantive attachment-sphere and original-certificate sphere constructions.",
            "finite-critical-cell-sphere"),
        H("Finite critical-cell sphere import facade"),
        Blocks(
            Paragraph(Text("This module imports FiniteCriticalCellSphere/AttachmentSphere and FiniteCriticalCellSphere/CertificateSphere. Their companion documents own all 65 original semantic Describe entries. The original Lean declaration namespaces remain unchanged; this facade adds no mathematical declarations. "))
        )));

}
