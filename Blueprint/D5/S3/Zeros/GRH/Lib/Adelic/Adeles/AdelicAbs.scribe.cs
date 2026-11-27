using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdelicAbsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adelic Abs", H("Adelic Abs"),
        Blocks(
            Paragraph(Text("Modulus of an idele: multiplicativity, continuity, product formula, invariance under conjugation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdelicAbs.ideleAbs_toAdele"),
                H("ideleAbs_toAdele"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The product formula: for a totally complex number field E and x in E^×, the principal idele of x has module ideleAbs equal to 1.")))))));
}
