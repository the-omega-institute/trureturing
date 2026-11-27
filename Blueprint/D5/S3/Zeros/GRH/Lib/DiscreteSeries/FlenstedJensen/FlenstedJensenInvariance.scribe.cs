using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class FlenstedJensenInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flensted Jensen Invariance", H("Flensted Jensen Invariance"),
        Blocks(
            Paragraph(Text("Flensted-Jensen integral is analytic and independent of the accretive splitting.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance.dsCoeff_eq_flenstedJensen"),
                H("dsCoeff_eq_flenstedJensen"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Independence of the splitting: for a parameter l = 2λ of some gap, g in U(diag ε) and a block diagonal matrix a such that a⁻¹g has positive definite hermitian part, ψ_λ(g) is the normalised integral HCParam.flenstedJensen at (a, a⁻¹g).")))))));
}
