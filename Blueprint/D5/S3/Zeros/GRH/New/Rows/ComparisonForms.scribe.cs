using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class ComparisonFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparison Forms", H("Comparison Forms"),
        Blocks(
            Paragraph(Text("Integral comparison forms seeing the twist through one number. There are forms on a definite unitary group, integral off the twist's conductor, short when untwisted and orthogonal as the congruence bound requires, whose descents to U(W_j) detect all good forms and see the twist only through one number made of Hecke L-values, and they cancel a lift's unknown volume. Integral forms pairing with a lift to an explicit L-value (pullback, seesaw) are known in low rank. Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; Y.-S. Lee, Hida family of theta lift from U(1) to definite U(2), 2024; Prasanna, Integrality of a ratio of Petersson norms, 2006.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/ComparisonForms.exists_comparison_forms"),
                H("exists_comparison_forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Comparison forms: there are γ_ϑ ≠ 0 with |γ_ϑ/γ_1|² = Γ(ϑ)/Γ(1) (Data.heckeValueProd), a linear surjection A from tables onto good forms on U(W_j), and linear Ξ_ϑ with u_ϑ*Ξ_ϑ = γ_ϑA (Data.goodLift), Ξ_ϑA*y tested, Ξ_ϑζ φ-integral for l prime to ϑ.levelNorm and ζ̄ integral at φ∘conj, and 𝗁‖Ξ_1ζ‖²_σ ≤ exp(2rB₀)∑_a‖σζ_a‖² (𝗁 = smallHookNumber).")))))));
}
