using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class FrameTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frame Theorem", H("Frame Theorem"),
        Blocks(
            Paragraph(Text("Kisin module of a crystalline lattice: frame, finite height, divisibility tests, spanning by nearly invariant vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/FrameTheorem.frame_theorem"),
                H("frame_theorem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Frame theorem, h the least bound of |jumps|: M = A_inf N, τ^h M ⊂ A_inf⊗L, τ^h(A_inf⊗L) ⊂ M, E^h φN ⊂ N. Also: S-linear maps A_inf → S keep relations, crystalline forms test divisibility in M, and for 3e ≤ p^l, eA ≤ p^l δ the vectors invariant modulo t^A span the valueFieldPoints of φ^l(M) up to p^{4δ}.")))))));
}
