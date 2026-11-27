using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class PairingDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairing Defs", H("Pairing Defs"),
        Blocks(
            Paragraph(Text("Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius (known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/PairingDefs.exists_isKilledBy_tateDual_tensor"),
                H("exists_isKilledBy_tateDual_tensor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j(s) lie in inertia, Y and L be potentially crystalline, and monic q, r in Z_p[X] kill (s,0) on Y and L. Then a monic e in Z_p[X] of degree ≤ deg q · deg r kills (s⁻¹,0) on Hom(Y ⊗ L, O(1)).")))))));
}
