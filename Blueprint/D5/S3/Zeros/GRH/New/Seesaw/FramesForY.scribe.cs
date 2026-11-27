using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class FramesForYDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frames For Y", H("Frames For Y"),
        Blocks(
            Paragraph(Text("Glued lattice is unimodular and real frames exist for the spaces Y_j.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/FramesForY.exists_frame_gradedGram"),
                H("exists_frame_gradedGram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let N > 0 be an integer, φ: R → ℂ a ring homomorphism, ε signs with exactly ⌊(s+1)/2⌋ minus signs. Some complex matrix y has yᴴφ(J)y = diag(ε), J the Gram matrix gradedGram of X ⊕ point plus string, and yᴴy = 1 if N = 1.")))))));
}
