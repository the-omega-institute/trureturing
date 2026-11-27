using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class DifferentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Different", H("Different"),
        Blocks(
            Paragraph(Text("Parameters N₀, d; fields K, E; infinite places as a group; CM type. Dictionary between places, Galois elements and residue classes; counts of all infinite places of E and of those congruent to 1 modulo N₀. Permutation of infinite places of E by an automorphism of ℂ over K. Roots of unity of K(ζ) are powers of ζ; the norm to K. Different of K(ζ) over K and ℚ, monogenicity, imaginary generator, its size.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/Different.prod_varpi_eq_rootDiscr_pow"),
                H("prod_varpi_eq_rootDiscr_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The product of the absolute values of ϖ_E over the infinite places of E equals rd_E raised to the number of infinite places, rd_E the root discriminant.")))))));
}
