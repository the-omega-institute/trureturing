using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class IdeleHilbert90Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Idele Hilbert90", H("Idele Hilbert90"),
        Blocks(
            Paragraph(Text("A minor of a generic matrix is a non-zero polynomial. Gauss q-binomial theorem as a sum over subspaces of a finite vector space. Functoriality of places and finite adeles under field maps and complex conjugation. Base change of finite adeles as topological modules; Galois invariants of finite adeles. Hilbert 90 for finite ideles under a cyclic Galois action.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/IdeleHilbert90.hilbert90_finite_idele"),
                H("hilbert90_finite_idele"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hilbert's Theorem 90 for finite ideles: if σ ∈ Gal(L/K) has finite order n and a finite adele u of L has ∏_{i<n} σ^i(u) = 1, then u·σ(c) = c for some invertible finite adele c.")))))));
}
