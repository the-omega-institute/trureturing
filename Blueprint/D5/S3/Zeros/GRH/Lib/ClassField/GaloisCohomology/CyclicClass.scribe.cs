using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class CyclicClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic Class", H("Cyclic Class"),
        Blocks(
            Paragraph(Text("Discrete Q/Z, continuous characters and the cyclic symbol δχ ∪ w.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/CyclicClass.cyclicClass"),
                H("cyclicClass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The class δχ ∪ w in H²(G,M) of the cocycle (g,h) ↦ carry(χ(g), χ(h))·w, biadditive in the character χ: G → ℚ/ℤ and the invariant w.")))))));
}
