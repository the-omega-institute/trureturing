using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class NormAbsValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm Abs Value", H("Norm Abs Value"),
        Blocks(
            Paragraph(Text("The adelic norm preserves the modulus; valuation of the local norm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/NormAbsValue.finIdeleAbs_adeleNorm"),
                H("finIdeleAbs_adeleNorm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For number fields L/K, the norm preserves the module of finite ideles: |N_{L/K}(y)| = |y| for every finite idele y of L.")))))));
}
