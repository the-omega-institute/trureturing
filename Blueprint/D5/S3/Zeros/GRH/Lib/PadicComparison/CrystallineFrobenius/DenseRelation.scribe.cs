using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.CrystallineFrobenius;

internal sealed class DenseRelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dense Relation", H("Dense Relation"),
        Blocks(
            Paragraph(Text("Transfer: rational cohomology of the base is the invariants of a Galois cover. Relation among field points of special fibre holds locally modulo z on tests.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/DenseRelation.exists_cancels_frobPow_locally"),
                H("exists_cancels_frobPow_locally"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let R be noetherian, W, Y proper, p ∈ 𝔴, ∑ n_i[Frob^{a_i}u_i(x)] = 0 at field points killing 𝔴. For some M: if z in O_C has p ∣ z^j and z^{M+1} dividing 𝔴O_C, the relation modulo (p, z) holds locally everywhere on p-adic points of W.")))))));
}
