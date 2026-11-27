using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class ChartScalarsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chart Scalars", H("Chart Scalars"),
        Blocks(
            Paragraph(Text("Maps θφ^{-n}; tilt elements fixed by the fixer of S approximated from S (Ax). S-linear maps extend from A_inf to B+; closure of S[1/p] and its properties.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/ChartScalars.z_dvd_of_dvd_E_pow_mul"),
                H("z_dvd_of_dvd_E_pow_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a chart and a in A_inf: if z divides E^k a in B^+, then z divides a in A_inf.")))))));
}
