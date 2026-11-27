using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class HodgeTateFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Frame", H("Hodge Tate Frame"),
        Blocks(
            Paragraph(Text("Base change of a bilinear pairing and its naturality. Admissibility passes to cyclotomic twists, subgroups, images; basic rules of the period action. Potentially crystalline representations are Hodge–Tate: frame over C_p and rank-many jumps.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/HodgeTateFrame.exists_hasJumps"),
                H("exists_hasJumps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j have open image, R be algebraic over Z_p, and T be finite free over R and potentially crystalline. Then at each γ: R → C_p the jumps of T, with multiplicity, form a multiset of cardinality the rank of T.")))))));
}
