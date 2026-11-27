using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class GaussSumSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauss Sum Sign", H("Gauss Sum Sign"),
        Blocks(
            Paragraph(Text("Sign of a Gauss sum fixed modulo 4 by orbits of order four.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/GaussSumSign.eq_one_of_orbits"),
                H("eq_one_of_orbits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let X be a finite abelian group without 2-torsion, f(f(x)) = −x, F an f-invariant function with values roots of unity, F(0) = 1, ∑F real, r ≡ 1 mod 4 an integer. If |c| = 1 and c·r^a = (∑F)·r^b, then c = 1.")))))));
}
