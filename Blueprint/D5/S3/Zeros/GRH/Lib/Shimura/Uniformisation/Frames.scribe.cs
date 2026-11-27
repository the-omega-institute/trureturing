using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class FramesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frames", H("Frames"),
        Blocks(
            Paragraph(Text("Adelic unitary similitude group, torsion module, frames of hermitian forms, reflections, signatures.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/Frames.mul"),
                H("mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If IsSignedFrame holds for (x, J), then for z in GL_n(E) and a unitary similitude g in GU it holds for (zxg, zJz⁻¹), with z acting on J through the embedding Φ v₀.")))))));
}
