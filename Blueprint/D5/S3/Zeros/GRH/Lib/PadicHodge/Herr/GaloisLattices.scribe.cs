using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Herr;

internal sealed class GaloisLatticesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois Lattices", H("Galois Lattices"),
        Blocks(
            Paragraph(Text("Artin–Schreier–Witt resolution over the tilt (known result; see Lib.PadicHodge.WachGamma.KisinModuleDefs).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Herr/GaloisLattices.thirdPairing_equivariant"),
                H("thirdPairing_equivariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The O-valued pairing β of Y ⊗ L with the extension of O by (Y ⊗ L)^∨(1) attached to P is equivariant into the Tate twist: β(gx, gt) = χ(j(g))·β(x, t) for g in Γ, with χ the cyclotomic character.")))))));
}
