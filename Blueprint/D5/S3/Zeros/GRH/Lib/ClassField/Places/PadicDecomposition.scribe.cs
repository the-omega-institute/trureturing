using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class PadicDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Padic Decomposition", H("Padic Decomposition"),
        Blocks(
            Paragraph(Text("Ax-Sen-Tate: fixed points in C_p are limits of fixed algebraic numbers. Decomposition group identified with Galois group of the p-adic completion (Krasner).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/PadicDecomposition.exists_inducesPlace"),
                H("exists_inducesPlace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("An embedding ι : Ω → Q̄_p pulling the integers back to A induces an open embedding j of the decomposition group of A in Gal(Q̄_p/ℚ_p), with j(g)(ιx) = ι(gx), whose image consists of the automorphisms fixing ι(K) pointwise.")))))));
}
