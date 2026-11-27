using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class SplittingCharOnU1Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting Char On U1", H("Splitting Char On U1"),
        Blocks(
            Paragraph(Text("Local values of base change; weight, powers and algebraicity of the splitting character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/SplittingCharOnU1.exists_chiFin_pow_eq_prod"),
                H("exists_chiFin_pow_eq_prod"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For Weil data on E and a finite idele x, there are n > 0 and y ∈ E^× such that xⁿ and y have the same valuation at every finite place and (υ(x)|x|^(−1/2))ⁿ = ∏_v Φ_v(ȳ), over the embeddings Φ_v of the CM type.")))))));
}
