using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.DiscreteSeries;

internal sealed class MinorExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minor Expansion", H("Minor Expansion"),
        Blocks(
            Paragraph(Text("Second-order expansion of log principal minors near 1 with absolute error constants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/DiscreteSeries/MinorExpansion.exists_principalMinor_eq_exp"),
                H("exists_principalMinor_eq_exp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let λ have gap h, X = g−1, ‖X‖ < 10⁻³ (Frobenius). Some y has ψ_λ(g) = HCParam.flenstedJensen(1,y) and, for k∈K and projectors P to sets p of lowest entries of λ, Δ_p(k*yk) = exp(tr(P log g)+‖[P,X]‖²/4+r), |r| ≤ 2·10⁵‖X‖(‖[P,X]‖²+‖[P,k]‖²).")))))));
}
