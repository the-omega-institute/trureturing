using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class FrobeniusOrbitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius Orbits", H("Frobenius Orbits"),
        Blocks(
            Paragraph(Text("Definitions: labels, cuspidal Green characters, their products, determinant characters, idempotents. Roots of an irreducible polynomial over a finite field form a Frobenius orbit.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/FrobeniusOrbits.labelIdem"),
                H("labelIdem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The element e_c = ∑ (Ξ_c(1)/|G|)·conj Ξ_c(g)·g of ℂ[G], G = GL_n(k), Ξ_c formed with faithfulChar, if c is a label of degree |n|; zero otherwise.")))))));
}
