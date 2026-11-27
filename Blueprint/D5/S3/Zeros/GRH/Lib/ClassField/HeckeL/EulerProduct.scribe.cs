using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeL;

internal sealed class EulerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler Product", H("Euler Product"),
        Blocks(
            Paragraph(Text("Finite ideles: principal, local, S-ideles, openness, compactness, almost-everywhere unramified characters. Euler products over primes of a number field, Dirichlet density, Dirichlet series identity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeL/EulerProduct.hasPrimeDensity_card_degree_one"),
                H("hasPrimeDensity_card_degree_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an extension L/K of number fields and c ∈ ℂ, the family v ↦ c·#{w above v : q_w = q_v} has density c over the primes of degree one of K, in the sense of HasPrimeDensity.")))))));
}
