using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qNormImageCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNormImageCertificate.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the order-three row action in the Nebe–Sloane P48q catalogue basis, every integral fixed row has an integral preimage under the cyclic norm.",
        H("The P48q Integral Norm Image"),
        Blocks(Describe.Lean(
            DescribeId.Create("nebe-order-three-fixed-is-norm-image"),
            DeclarationHandle.Create(Prefix + "nebeOrderThree_fixed_is_norm_image"),
            H("Every integral fixed row is an integral norm image"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Nebe),
            Blocks(
                Paragraph(Text("Let A be the fourth power of the first generator in the Nebe–Sloane catalogue’s "
                    + "P48q entry, acting on rows by right multiplication. Write I for the identity matrix and "
                    + "N = I + A + A² for the cyclic norm. For every row v indexed by Fin 48 with integer "
                    + "entries and satisfying vA = v, there exists a row x with the same index set and "
                    + "integer entries such that xN = v.")),
                Paragraph(Text("Embed the adjugate table for the selected 16-by-16 minor of N in a matrix B, "
                    + "placing the entries at the minor’s column indices by row indices. Two exact rowwise "
                    + "product checks give NBN = 463360 N. The cube identity A³ = I gives N² = 3N. Thus "
                    + "C = B − 154453 I is integral and satisfies NCN = N, since 463360 − 3 · 154453 = 1.")),
                Paragraph(Text("A fixed row satisfies vA² = v and hence vN = 3v. Multiplying NCN = N on "
                    + "the left by v gives 3(vC)N = 3v. Coordinatewise cancellation of 3 over the integers "
                    + "gives (vC)N = v, so the witness is x = vC."))),
            DescribeRole.Theorem))));
}
