using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction;

internal sealed class HermitianActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian Action", H("Hermitian Action"),
        Blocks(
            Paragraph(Text("Polarised torus with multiplications: canonical multiplier, normalised translations, isogeny kernels and degree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/HermitianAction.normShift_sum_eq_char_smul"),
                H("normShift_sum_eq_char_smul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let f be fixed by the normalised translations by aL, ξ a character of the finite kernel of a on V/L, and s = ∑_k ξ(−k)·(translate of f by ak). If ay ∈ L, the normalised translation by ay multiplies s by ξ(y).")))))));
}
