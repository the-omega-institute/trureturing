using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup;

internal sealed class ThetaStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Structure", H("Theta Structure"),
        Blocks(
            Paragraph(Text("Symmetric theta coordinates are unique; K(L) is killed by the order of the index set.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/ThetaStructure.card_nsmul_eq_zero_of_lift"),
                H("card_nsmul_eq_zero_of_lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over a ring R, let global functions on A be constant and (N, c) a theta structure indexed by finite H, with N a projective embedding whose coordinates span H⁰(N). Then |H| kills every section y whose translation lifts to N (via Ψ); over a local ring R these are exactly the sections y in the kernel K([N]).")))))));
}
