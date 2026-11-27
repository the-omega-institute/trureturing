using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class ContinuousCocyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous Cocycles", H("Continuous Cocycles"),
        Blocks(
            Paragraph(Text("Continuous cocycles, coboundaries, H² and functoriality for discrete modules.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/ContinuousCocycles.charRep"),
                H("charRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an R-module M and a character χ: G → R^×, the representation of G on M in which g acts as the scalar χ(g).")))))));
}
