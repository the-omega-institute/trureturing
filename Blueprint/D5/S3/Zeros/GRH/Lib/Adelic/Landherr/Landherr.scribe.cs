using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Landherr;

internal sealed class LandherrDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Landherr", H("Landherr"),
        Blocks(
            Paragraph(Text("Landherr's Hasse principle for hermitian forms, and weak approximation for unitary groups. The form here covers only adelically unimodular spaces of equal signature over a CM field containing the roots of unity of order 5040. It is proved from Hasse's norm theorem instead of Hasse-Minkowski, and approximation uses a Cayley transform with a norm-one scalar. Source: W. Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abh. Math. Sem. Hamburg 11 (1936) 245-248; M. Kneser, Lectures on Galois cohomology of classical groups, TIFR 47 (1969), §5.5.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Landherr/Landherr.exists_eq_move"),
                H("exists_eq_move"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Landherr's theorem for spaces with a point: over stably unramified E (StablyUnram), any two spaces V, W with the same signs differ by a rational change of coordinates a and moving the point by some g in G.")))))));
}
