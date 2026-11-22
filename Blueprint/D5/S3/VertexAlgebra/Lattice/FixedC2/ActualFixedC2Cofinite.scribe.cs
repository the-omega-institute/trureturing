using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2CofiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual sign-fixed Leech lattice vertex algebra has a finite-dimensional intrinsic C2 quotient.",
        H("C2 Cofiniteness of the Sign-Fixed Leech Lattice Vertex Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-leech-cofinite"),
                DeclarationHandle.Create(Prefix + "leech_fixed_c2_cofinite"),
                H("The intrinsic fixed quotient is finite-dimensional over the complex numbers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The quotient is the sign-fixed carrier of the actual Leech lattice "
                        + "vertex algebra modulo the complex span of actual (-2)-products of pairs of "
                        + "fixed states.")),
                    Paragraph(Text("Charge descent shows that the quotient is spanned by the orbit "
                        + "images for the finitely many charges in the closed Gram-coordinate box. "
                        + "The orbit of zero is exactly the fixed vacuum-charge space, since support "
                        + "at zero is equivalent to being the insertion of a single oscillator "
                        + "polynomial there. The bounded even words give a finite spanning family "
                        + "for its image. For every nonzero orbit the image is contained in the span "
                        + "of neutral multiples of the ground and first oscillator classes, which is "
                        + "also finite-dimensional. The finite sum of these subspaces is the whole "
                        + "quotient.")),
                    Paragraph(Text("Abe, arXiv:math/0311210, Theorem 7.1(2), records fixed lattice C2 "
                        + "cofiniteness and cites Yamskulna. The formal proof here uses the actual "
                        + "Leech state-field modes and the explicit short charge and oscillator reductions."))),
                DescribeRole.Theorem))));
}
