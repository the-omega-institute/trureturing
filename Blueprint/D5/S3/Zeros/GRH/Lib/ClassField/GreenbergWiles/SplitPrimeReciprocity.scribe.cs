using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class SplitPrimeReciprocityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Split Prime Reciprocity", H("Split Prime Reciprocity"),
        Blocks(
            Paragraph(Text("Power residue symbols of S-units give exactly the relations on tame ramification of cocycles.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.power_residue_reciprocity"),
                H("power_residue_reciprocity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let U fix V, mV = 0, γ_i satisfy IsTameGeneratorFor, and ζ^(b(y)_i) = φ_i r/r for N-units y = r^m. Trivialised cocycles z obey ∑ b(gy)_i g⁻¹z(γ_i) = 0 and vanish on U if all z(γ_i) = 0. For totally complex fixed field, ∑ b(gy)_i f(i,g) = 0 for all y makes (∑_g f(i,g) ga)_i some (z(γ_i))_i.")))))));
}
