using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class PsiDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Psi Decay", H("Psi Decay"),
        Blocks(
            Paragraph(Text("Decay of the coefficient like (2/‖g‖)^h, constant free of the parameter.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/PsiDecay.norm_dsCoeff_le_pow"),
                H("norm_dsCoeff_le_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a parameter l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε): |ψ_λ(g)| ≤ (2/‖g‖)^c, with the operator norm.")))))));
}
