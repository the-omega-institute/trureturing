using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class ActualParityIrreducibleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/ActualParityIrreducible.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irreducibility of each entire actual parity sector under all fixed-source physical modes.",
        H("Finite Borcherds elimination and opposite-parity closure"),
        Blocks(
            Paragraph(Text("Let D be any native integral symmetric lattice datum with even "
                + "diagonal and hu:IsUnit D.G.det. Let s be 1 or -1. The carrier is the entire "
                + "production paritySpace D hu s inside ActualTensor D hu. Let S be any complex "
                + "submodule of this space. Sources are every original theta-fixed source "
                + "a:FixedCarrier D; modes are every integer physical mode of fixedParitySlice.")),
            Describe.Lean(
                DescribeId.Create("fixed-parity-slice-irreducible"),
                DeclarationHandle.Create(Prefix + "fixedParitySlice_irreducible"),
                H("Every fixed-source mode-stable sector submodule is bottom or top"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("If S is stable under all these sources and modes, then "
                    + "S is bottom or top. There is no assumed restricted irreducibility, "
                    + "generation, positivity, rank24, preferred-model identification, finite "
                    + "mode replacement or nonzero-sector hypothesis. Rank zero and the zero "
                    + "sector are included."))),
                DescribeRole.Theorem),
            Paragraph(Text("The new finite closure argument starts with fullLaw(A,B,U,gamma) "
                + "at one actual vector w. Suppose every U(r)[[k]] w belongs to W. Choose l "
                + "above the actual A-mode cutoff at w, set p=l, q=n and r=m-l. Every second "
                + "family term vanishes since A[[l+j]]w=0. The leading first-family term is "
                + "A[[m]]B[[n]]w. Its higher terms are A[[m-j]]B[[n+j]]w. Strong induction on "
                + "the natural distance of n below B's actual cutoff proves their membership. "
                + "The finite left-family sum already lies in W, so subtracting the finite "
                + "higher first-family sum isolates the desired product. No infinite sum is "
                + "treated as a convergent analytic series and no support is discarded.")),
            Paragraph(Text("Map S to the actual tensor by the literal parity-space inclusion; "
                + "call the image E. Let O be the complex span of all odd-source physical modes "
                + "acting on E. Source mode_eigenvalue_selection makes source iterates have the "
                + "product theta eigenvalue. The existing first_eigen_arbitrary_second supplies "
                + "the original all-state fullLaw, without a second-source eigen premise. The "
                + "finite elimination argument closes even times odd into O and odd times odd "
                + "into E. In the latter case the original iterate has lift 2: physicalSlice "
                + "at mode n has raw exponent -2*n-4, exactly fixed lift 0 at mode n+1. This "
                + "shift is retained explicitly. Even stability closes even times E.")),
            Paragraph(Text("Split each arbitrary source using the existing theta involution "
                + "into plusPart and minusPart. correctedField_theta kills every raw exponent "
                + "of unmatched parity; every matching raw exponent is an integer physical mode "
                + "with lift 0 or 1. Consequently T=E+O is stable under every raw coefficient "
                + "of every full source. The accepted correctedField_irreducible applies to T, "
                + "not directly to S. Nonzero S makes T nonzero, hence T is the whole tensor.")),
            Paragraph(Text("correctedField_target_parity puts O in the opposite actual "
                + "parity eigenspace. If a vector of sector s is y+z with y in E and z in O, "
                + "applying actualParity gives s*z=(-s)*z. Since s is 1 or -1 over the complex "
                + "numbers, z=0. Thus the intersection of T with sector s is exactly E. When "
                + "T is top, every sector vector is in S. This completes the full algebraic "
                + "sector argument using the original D, hu, actualParity and production fields.")),
            Paragraph(Text("This is classical order-two twisted lattice module mathematics; "
                + "no novelty is claimed. It does not construct orbifold gluing, a "
                + "two-twisted intertwining operator, a Monster action, all-grade fusion, "
                + "or complete CFT, string-theory or AdS/CFT bridges.")))));
}
