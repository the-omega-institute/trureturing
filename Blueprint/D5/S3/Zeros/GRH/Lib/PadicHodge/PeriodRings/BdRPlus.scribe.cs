using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class BdRPlusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bd R Plus", H("Bd R Plus"),
        Blocks(
            Paragraph(Text("B_max^+ is a domain, kernel of theta; B_dR^+ is a discrete valuation ring.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/BdRPlus.injective_BPlus_Bcris"),
                H("injective_BPlus_Bcris"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The localisation map B^+ → B = B^+[1/μ] is injective.")))))));
}
