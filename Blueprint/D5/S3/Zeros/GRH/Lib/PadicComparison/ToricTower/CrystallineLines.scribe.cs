using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.ToricTower;

internal sealed class CrystallineLinesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Lines", H("Crystalline Lines"),
        Blocks(
            Paragraph(Text("Periodic functions represent root systems of a unit; Kummer tower has Wang sequence. Poincaré lemma: gamma minus one on divided power envelopes of root systems.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/ToricTower/CrystallineLines.rootSystemsAreLines_crysTest"),
                H("rootSystemsAreLines_crysTest"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("On p-torsion-free p-complete A_max-algebras D over A, root systems in D/𝔡(D) (characters of ℚ≥0) of a unit y of A/𝔡(A) form a line for B_max ⊗ D: their homotopy quotient by the twist of rootSystems has the cohomology of h_A.")))))));
}
