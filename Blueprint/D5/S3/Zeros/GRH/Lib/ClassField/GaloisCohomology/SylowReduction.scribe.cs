using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class SylowReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sylow Reduction", H("Sylow Reduction"),
        Blocks(
            Paragraph(Text("Shapiro's lemma in degrees 0–2, corestriction, cor∘res = index, projection formula for symbols. Hilbert 90 for continuous cocycles, Kummer cocycles, cup product as cyclic symbol. Sylow reduction of H² statements to cyclic steps of prime degree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/SylowReduction.mem_of_prime_step"),
                H("mem_of_prime_step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let α in H²(Γ, M) die on open normal W. Suppose that for open U ⊇ W and open normal V ⊇ W of prime index in U, if α − s (s in S) dies on V, some α − s' dies on U. Then α ∈ S.")))))));
}
