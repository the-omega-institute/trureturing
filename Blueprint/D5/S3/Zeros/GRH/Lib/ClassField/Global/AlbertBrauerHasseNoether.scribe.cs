using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Global;

internal sealed class AlbertBrauerHasseNoetherDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Albert Brauer Hasse Noether", H("Albert Brauer Hasse Noether"),
        Blocks(
            Paragraph(Text("Global class field theory, covering Albert–Brauer–Hasse–Noether, reciprocity, existence and norms. Only finite ideles are used, real places are handled by total positivity, and existence is proved only for totally complex fields. Reciprocity starts from cyclotomic characters of prime conductor, and the auxiliary character is chosen by B. H. Neumann's covering lemma. Source: J. S. Milne, Class Field Theory (v4.03, 2020), VI 4.9, VII 4–9, VIII 4; Tate, Global class field theory, in Cassels–Fröhlich 1967, ch. VII; H. Hasse, Die Struktur der R. Brauerschen Algebrenklassengruppe, Math. Ann. 107 (1933) (reciprocity from the sum formula).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Global/AlbertBrauerHasseNoether.albert_brauer_hasse_noether"),
                H("albert_brauer_hasse_noether"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Albert–Brauer–Hasse–Noether: a class in Br(K) = H²(Γ, Ω^×), K a number field, is zero if it dies on every decomposition group at a finite place and on some open subgroup containing all complex conjugations.")))))));
}
