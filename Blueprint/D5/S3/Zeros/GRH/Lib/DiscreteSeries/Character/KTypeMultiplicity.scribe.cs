using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character;

internal sealed class KTypeMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "K Type Multiplicity", H("K Type Multiplicity"),
        Blocks(
            Paragraph(Text("Weyl character and denominator formulas for U(p)×U(q); conjugacy into the torus. K-type multiplicities of discrete series: integer, one at lowest type, supported in cone.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/KTypeMultiplicity.exists_kType_multiplicity"),
                H("exists_kType_multiplicity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Multiplicity of a K-type. Let l = 2λ have gap 500n³+A, n ≥ 1, ν be K-dominant. Then g ↦ ∫_K χ̄_ν(k)ψ_λ(g⁻¹kg)dk is integrable, and deg_λ times its integral is some m∈ℕ; m = 1 for ν = Λ = HCParam.lowestKType l, and m ≠ 0 forces ν−Λ∈HCParam.rootCone l.")))))));
}
