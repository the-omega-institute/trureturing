using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class KerrSchildWeylDoubleCopy4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/LieTheory/benincasacachazo2007smatrix");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Null Kerr–Schild updates preserve the metric determinant, and the signed Coulomb square gives the Schwarzschild Weyl quartic.",
        H("Kerr–Schild metric algebra and the Coulomb Weyl square"),
        Blocks(
            Result("eta-square", "eta_square", "The background metric squares to the identity",
                "The diagonal entries of the metric η are −1, 1, 1 and 1, so their squares are all one."),
            Result("eta-sharp", "eta_sharp", "Raising a covector",
                "Multiplying a column k by the metric negates its time coordinate and preserves its spatial coordinates."),
            Result("vec-eta", "vec_eta", "Raising a row covector",
                "Right multiplication of k by the metric has the same coordinate effect as left multiplication."),
            Result("sharp-dot", "sharp_dot", "The raised contraction is the Minkowski square",
                "Taking the ordinary coordinate dot product of the raised covector with k gives −k₀²+k₁²+k₂²+k₃²."),
            Result("ks-inverse", "ks_inverse", "Exact inverse of a null Kerr–Schild update",
                "In both multiplication orders, the cross terms of the metric and proposed inverse cancel. "
                + "The quadratic term contains the contraction kᵀηk, which vanishes for a null covector. "
                + "Both products are the identity for every real metric scalar."),
            Result("ks-det", "ks_det", "The determinant of the null update is minus one",
                "Multiplication by η writes the updated metric as identity plus an outer product. "
                + "The rank-one determinant lemma gives 1+φ kᵀηk, which is one. The determinant of η is minus one."),
            Result("coulomb-raw", "coulomb_raw_square", "The raw square in the negative scalar convention",
                "For nonzero mass M, charge Q and radius r, form the trace-free outer square of the radial electric field (0,0,Q/r²). "
                + "Dividing by S=−Q²/(3Mr) gives the diagonal entries M/r³, M/r³ and −2M/r³.", acknowledge: true),
            Result("coulomb-schwarzschild", "coulomb_to_schwarzschild_stf", "The Coulomb square in the Schwarzschild tide convention",
                "With the curvature sign of the Schwarzschild electric tide used here, the map is the negative of the preceding scaled square. "
                + "Its electric tensor is diagonal with entries −M/r³, −M/r³ and 2M/r³. The Weyl tensor is built by applying "
                + "the inverse electric–magnetic equivalence to this tensor and zero magnetic part.", acknowledge: true),
            Result("schwarzschild-quartic", "schwarzschild_weylQuartic", "The Schwarzschild Weyl quartic",
                "The two transverse diagonal entries agree and the off-diagonal entries vanish. "
                + "The Weyl-to-quartic coefficient map leaves only the coefficient of X², equal to 24M/r³."),
            Result("schwarzschild-tide", "schwarzschild_tide_eval", "Schwarzschild screen tides",
                "The complex contraction on a finite ray z is (24M/r³)z². "
                + "At infinity the contraction is the quartic coefficient of degree four and is zero. The finite contraction also vanishes at z=0."),
            Result("schwarzschild-type-d", "schwarzschild_is_type_D", "Two distinct projective double roots",
                "When M and r are nonzero, the homogeneous quartic is a nonzero scalar times z²w². "
                + "The two linear factors have independent coefficient vectors, so their roots are distinct and each has multiplicity two. "
                + "They are the finite origin and the point at infinity.")),
        []));

    private static DocumentBlock Result(string id, string name, string title, string prose, bool acknowledge = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            acknowledge ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
