using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class WeilDataOfEDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weil Data Of E", H("Weil Data Of E"),
        Blocks(
            Paragraph(Text("Decomposition of primes and Frobenius in a cyclotomic extension of an imaginary quadratic field. Weil data for E: cyclotomic unit, idele of half the different, splitting character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/WeilDataOfE.v_alpha_mul_relDifferentGen"),
                H("v_alpha_mul_relDifferentGen"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At every finite place w of E, the w-component of α·ᾱ·P'(ζ) is a unit, where α = Parameters.α and P'(ζ) = Parameters.relDifferentGen generates the different of E/K.")))))));
}
