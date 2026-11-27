using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.LocalHeight;

internal sealed class IsogenyIntegralityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isogeny Integrality", H("Isogeny Integrality"),
        Blocks(
            Paragraph(Text("Transport of sections and points to a Galois conjugate curve. Sections bounded by the local height are integral in the formal parameter. Roots-of-unity filter on power series; iterating an Artin-Schreier relation. Torsion translates and isogeny pull-backs of the CM theta function are integral series.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/LocalHeight/IsogenyIntegrality.norm_le_one_of_isogeny"),
                H("norm_le_one_of_isogeny"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a complex number a satisfies aΛ ⊂ Λ' for the lattices of two CM data for d (a prime ≡ 7 mod 8), then a is p-adically integral: |ι(a)|_p ≤ 1.")))))));
}
