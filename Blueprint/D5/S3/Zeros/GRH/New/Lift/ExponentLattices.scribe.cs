using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class ExponentLatticesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponent Lattices", H("Exponent Lattices"),
        Blocks(
            Paragraph(Text("Lattices with prescribed exponents at each E_a, cost of Galois steps, retraction API.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/ExponentLattices.smul_sub_mem_zTauUnit_smul_of_deep"),
                H("smul_sub_mem_zTauUnit_smul_of_deep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If x lies in 𝒩, g in Γ', and gx − x has exponents c at the letter i, then (gx − x)/(zτ) also has exponents c at i.")))))));
}
