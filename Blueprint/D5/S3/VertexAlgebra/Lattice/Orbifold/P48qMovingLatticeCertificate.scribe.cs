using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qMovingLatticeCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingLatticeCertificate.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the order-three row action in the Nebe–Sloane P48q catalogue basis, the integral norm kernel equals the integral difference image.",
        H("The P48q Integral Moving Lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("nebe-order-three-moving-exact"),
            DeclarationHandle.Create(Prefix + "nebeOrderThree_moving_exact"),
            H("The integral norm kernel equals the integral difference image"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Nebe),
            Blocks(
                Paragraph(Text("Let A be the fourth power of the first generator in the Nebe–Sloane catalogue’s "
                    + "P48q entry, acting on rows by right multiplication. Write I for the identity matrix, "
                    + "N = I + A + A² for the cyclic norm, and B = I − A. For every row x indexed by Fin 48 "
                    + "with integer entries, xN = 0 if and only if there is a row y with the same index set "
                    + "and integer entries such that yB = x.")),
                Paragraph(Text("The kernel checks the entries of the integral matrix identity "
                    + "I = UB + NV + 3E, where U, V and E are the certificate matrices. The cube identity "
                    + "A³ = I gives BN = 0, so every row of the form yB is in the norm kernel.")),
                Paragraph(Text("If xN = 0, the certificate gives x = (xU)B + 3(xE). Multiplying this "
                    + "identity by N and cancelling 3 in each integer coordinate gives (xE)N = 0. "
                    + "Because (2I + A)B = 3I − N, the integral row y = xU + (xE)(2I + A) satisfies yB = x."))),
            DescribeRole.Theorem))));
}
