using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli;

internal sealed class UniversalFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal Family", H("Universal Family"),
        Blocks(
            Paragraph(Text("Analytic families immerse, finitely many meet every point; covers have only the expected points. Universal theta family over a smooth projective base, uniformised by balls.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/UniversalFamily.nonempty_universalFamily"),
                H("nonempty_universalFamily"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let D be PEL data and R ⊂ E a localisation of O_E whose maximal ideals lie over primes good for D (PEL.IsGoodAt). Then a universal theta family UniversalFamily exists: its base is projective and smooth over R, with dense, holomorphically modelled complex objects.")))))));
}
