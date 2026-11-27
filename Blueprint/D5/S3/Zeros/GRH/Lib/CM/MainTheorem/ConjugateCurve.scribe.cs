using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.MainTheorem;

internal sealed class ConjugateCurveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate Curve", H("Conjugate Curve"),
        Blocks(
            Paragraph(Text("Conjugate CM curve, conjugation of isogenies, theta function and its torsion translates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/MainTheorem/ConjugateCurve.exists_taylorVia_twistedTranslate_theta"),
                H("exists_taylorVia_twistedTranslate_theta"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let d be a prime ≡ 7 mod 8, σ ∈ Aut(ℂ/K), a₁(D) = σa₁(C), Λ_C = Ω𝒪_K, S ⊂ K finite. Some v ∈ Λ_D has: for all x ∈ S, σ maps the Taylor series at 0 of U_{xΩ}θ_C to that of U_{xv}θ_D.")))))));
}
