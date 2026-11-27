using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.DiscreteSeries;

internal sealed class RestrictionLemmaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restriction Lemma", H("Restriction Lemma"),
        Blocks(
            Paragraph(Text("Period of deep-level Poincaré series equals main term up to explicit error. Explicit lower bound for oscillating integral of two coefficients over a subgroup. Cauchy matrix of controlled size at which the phases of a restriction period cancel.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma.exists_isTwoFactor_restriction"),
                H("exists_isTwoFactor_restriction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l, l' satisfy IsSteep for X, B ≥ 1 and M, M+1, with M even and l' of some gap. Some ω in U(diag(ε) ⊕ 1) has ‖ω‖ ≤ (n+1)²(6B)^{2M+1}, and j(r) = (r, ω⁻¹(r ⊕ 1)ω) satisfies IsTwoFactor for l, −l', with phase HCParam.phase zero and second component of j(r) − 1 equal to ω⁻¹((r−1) ⊕ 0)ω.")))))));
}
