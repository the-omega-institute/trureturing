using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMNativeLaurentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Laurent coefficients of four inverse lowerings",
        H("Occupation readout and chart transport"),
        Blocks(
            Result("four-m-native-occupation-fourier-overlap", "native_occupation_fourier_overlap",
                "Native sector Fourier overlap",
                "For a rank-24 positive definite lattice with unit Gram determinant, distinct marked occurrences, "
                + "a real argument strictly between zero and one, and an A parameter equal to the square of a "
                + "complex number of norm less than one, evaluate each chart in native slot order. Multiply "
                + "its occupied-sector readout by the cube of one minus the chart parameter and the product "
                + "of lifted scales. On the upper A continuation, the lower D value is the finite Fourier sum "
                + "of A with factor 2 to power −12. "
                + "The B value has the additional quadratic sign and inverse twelfth power of the A period root."),
            Result("four-m-project-occupations-inverse-readout", "projectOccupations_eq_inverse_readout",
                "Diagonal left selector and right detector",
                "For rank 24 with positive definite Gram form and unit determinant, use nonzero ground "
                + "vectors and homogeneous left oscillator inputs of weights H and K. At charge energy zero "
                + "the left selector is one on every supported lowered pair. The projected occupation sum "
                + "is the readout of their inverse flows cut off at H−1 and K−1, times (−1) to power K, "
                + "with the right detector retained. This detector is one precisely when the doubled weight "
                + "difference w of the right occupations is even and the requested mode is −1+w/2."),
            Result("four-m-projected-lowering-sum", "projected_lowering_sum",
                "Finite outgoing inverse lowering",
                "Under the same lattice hypotheses with all four inputs homogeneous of weights H,K,L,J "
                + "on nonzero ground vectors, impose J=H+K+L−s−2. Sum the projected occupations over "
                + "outgoing lowering degrees ell below N using loweringWeight and right mode s+ell−H−K+1. "
                + "Both diagonal selectors are then one on support. The resulting four-slot readout has "
                + "inverse flows in the first two slots of cutoffs H−1 and K−1 and in the fourth slot of "
                + "cutoff N, with coefficient (−1) to power s+2 times (−1) to power K."),
            Result("four-m-lowered-native-sector-laurent", "lowered_native_sector_eq_laurent",
                "Actual Laurent coefficient of four finite inverse lowerings",
                "For a positive definite rank-24 lattice with unit Gram determinant, take four creation "
                + "words formed from a list of marked occurrences, with tensor weights H,K,L,J on nonzero "
                + "ground vectors and J=H+K+L−s−2. For any real chart argument with nonzero chart "
                + "parameter t and any charge class, the native sector readout of the four lowered words "
                + "equals the native Laurent evaluation multiplied by (−t) to the chart exponent and the "
                + "chart sign. In A the native order is P,Q,R,S, the exponent is H+K and the sign is "
                + "(−1) to power K. In B the order is Q,R,P,S with exponent K+L. The choice upperA = true "
                + "takes the upper A continuation and the lower D lip. In D the order is P,R,Q,S "
                + "with exponent H+L. Both B and D use sign (−1) to power s+2 times "
                + "(−1) to power L and the outgoing lowering cutoff J−1. The finite diagonal selectors "
                + "and the inverse-flow identity cancel the Laurent normalization exactly."),
            Result("four-m-native-laurent-fourier-overlap", "native_laurent_fourier_overlap",
                "Fourier overlap of actual Laurent evaluations",
                "For the same lattice and homogeneous marked creation words with nonzero ground vectors, "
                + "distinct occurrences and the signed output weight relation, assume 0<x<1 and that the "
                + "A parameter is the square of a complex number of norm less than one. Normalize each "
                + "native Laurent value by its chart power and sign, the cube of one minus its parameter "
                + "and the product of lifted scales. On the upper A continuation, the normalized lower D value "
                + "is the Fourier sum of A with factor 2 to power −12. The B value is the "
                + "quadratically signed Fourier sum with "
                + "the same factor and the inverse twelfth power of the A period root."))));

    private static DocumentBlock Result(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
