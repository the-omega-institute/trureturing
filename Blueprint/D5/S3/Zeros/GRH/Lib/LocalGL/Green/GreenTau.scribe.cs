using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class GreenTauDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Green Tau", H("Green Tau"),
        Blocks(
            Paragraph(Text("Cuspidality, independence of choices and orthogonality of the characters of irreducible polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/GreenTau.rankInner_greenTau"),
                H("rankInner_greenTau"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let T be injective, P monic irreducible, P(0) ≠ 0. On GL_{deg P}(k), ⟨τ_P,τ_S⟩ is 1 if P = S, else 0, for S monic irreducible with S(0) ≠ 0; if P(1) ≠ 0, Hall.skew of τ_P in degree deg P kills the constant function 1.")))))));
}
