using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class PsiBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Psi Basic", H("Psi Basic"),
        Blocks(
            Paragraph(Text("Basic properties of the coefficient: polar formula, inversion, conjugation, values on K.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/PsiBasic.dsCoeff_of_mem_maxCompactU"),
                H("dsCoeff_of_mem_maxCompactU"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a parameter λ of gap h and k in K = U(diag ε) ∩ U(n), ψ_λ(k) = m_Λ(k), the product of principal minors of weight Λ = λ + ρ − 2ρ_c.")))))));
}
