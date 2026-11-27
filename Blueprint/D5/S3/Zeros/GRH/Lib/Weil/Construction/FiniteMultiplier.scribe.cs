using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class FiniteMultiplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Multiplier", H("Finite Multiplier"),
        Blocks(
            Paragraph(Text("Finite multiplier of the splitting through saturating matrices; multiplicativity, phase, lattice index.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteMultiplier.finMultiplier_eq_of_supportedOn"),
                H("finMultiplier_eq_of_supportedOn"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be a set of finite places disjoint from S̄, and g in G_f supported on S ∪ S̄. If a equals g above S and 1 elsewhere, then Δ_f(g) = |Δ_f(a)|² · conj χ_f(det a).")))))));
}
