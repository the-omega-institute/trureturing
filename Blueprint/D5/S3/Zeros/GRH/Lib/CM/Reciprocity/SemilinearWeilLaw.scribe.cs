using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.Reciprocity;

internal sealed class SemilinearWeilLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semilinear Weil Law", H("Semilinear Weil Law"),
        Blocks(
            Paragraph(Text("Semilinear map intertwining Heisenberg translations intertwines the finite Weil representation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/Reciprocity/SemilinearWeilLaw.semilinear_intertwines_weil"),
                H("semilinear_intertwines_weil"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L be σ-semilinear with values in 𝒲_f, Lϱ(x) = ϱ(bx)L on 𝒲_f, σψ₀(z) = ψ₀(bb̄z), R ∩ R̄ = ∅. Then b is a unit, Lω(g) = (σΔ(g)/Δ(g))ω(g)L on 𝒲_f, and some c and unitary adele z have L vac = cω(z)vac, L(Ψ⊗vac) = cω(z)(σΨ⊗vac), Ψ Schwartz–Bruhat above R.")))))));
}
