using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character;

internal sealed class SectorBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sector Bound", H("Sector Bound"),
        Blocks(
            Paragraph(Text("Haar measure of U(p,q) as the measure of its open orbit on flags. Weyl's dimension formula for U(n), as the mean square of the highest coefficient. Lower bound for products of principal minors of conjugated positive diagonal matrices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/SectorBound.le_norm_weightMinors_twoPowDiagConj"),
                H("le_norm_weightMinors_twoPowDiagConj"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let u be unitary, l, f integer vectors, m an integer, f_a+|m| ≤ f_c whenever l_c < l_a, and h ≤ |l_i−l_j|, h natural. Then (|u_ij|² 2^m)^h·|m_l(D)| ≤ |m_l(u*Du)|, where D = diag(2^{f_a}).")))))));
}
