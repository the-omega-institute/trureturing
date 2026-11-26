using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Mass;

internal sealed class MassRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass Ratio", H("Mass Ratio"),
        Blocks(
            Paragraph(Text("Ratio of consecutive masses of unimodular hermitian lattices, explicit error uniform in field.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Mass/MassRatio.abs_log_mass_ratio_sub_le"),
                H("abs_log_mass_ratio_sub_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a CM field E with Weil data, f infinite places and root discriminant rd: if 8f ≤ 2^u and j ≥ 4u + 12, then log(mass_{j+1} / mass_j) differs from f·log(rd^{j+1/2} j! / (2π)^{j+1}) by at most 2/2^u.")))))));
}
