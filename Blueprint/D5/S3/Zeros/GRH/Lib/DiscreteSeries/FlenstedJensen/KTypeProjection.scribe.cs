using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class KTypeProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "K Type Projection", H("K Type Projection"),
        Blocks(
            Paragraph(Text("Lowest K-type occurs once; K-types outside the cone above it do not occur.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/KTypeProjection.integral_conj_weightMinors_mul_dsCoeff"),
                H("integral_conj_weightMinors_mul_dsCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l = 2λ be a parameter of some gap, x, b in U(diag ε), ν K-dominant. Then ∫_K conj(m_ν(k)) ψ_λ(xkb) dk is c_Λ ψ_λ(x)ψ_λ(b), c_Λ = ∫_K |m_Λ|², if ν = Λ, and 0 if ν ≠ Λ and ν − Λ lies outside HCParam.rootCone.")))))));
}
