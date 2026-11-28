using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class DeRhamValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "De Rham Values", H("De Rham Values"),
        Blocks(
            Paragraph(Text("Value fields in B_dR, filtration lemmas, S-linear retractions preserve B_dR^+ relations.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/DeRhamValues.smul_sub_mem_hodgeFil_of_valueField"),
                H("smul_sub_mem_hodgeFil_of_valueField"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let x in B_dR^+ lie in the field 𝒦_a (Lift.KummerChart.valueField) and g, t_1, …, t_m in Γ'. If φ^a(E) divides (g − 1)∑ t_l s for all s in S, then (g − 1)∑ t_l x lies in tB_dR^+.")))))));
}
