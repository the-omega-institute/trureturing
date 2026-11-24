using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMAssignedOccupationDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMAssignedOccupation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed four-point overlap in native occupations",
        H("Compact affine coefficients of the original chart fields"),
        Blocks(
            D("four-m-compact-mode", "compactMode", "Tagged native mode", DescribeRole.Definition,
                Text("Send a surviving mode to its colour and oscillator index in the common finite "
                    + "support, with leg and orientation selected by the chart flags at its puncture.")),
            D("four-m-compact-covariance", "compactCovariance", "Compact native covariance",
                DescribeRole.Definition,
                Text("Restrict the slit covariance of A or B, or the true D-lip covariance, to the "
                    + "compact tagged support and evaluate it at the chart parameter.")),
            D("four-m-compact-mean", "compactMean", "Compact native mean", DescribeRole.Definition,
                Text("Multiply the chart's native linear entry at a tagged oscillator by the "
                    + "lattice pairing of its unit colour charge with the fixed charge. Use the "
                    + "slit entry in A and B and the true lip entry in D.")),
            D("four-m-mode-array-pullback", "mode_array_pullback", "Native arrays in compact coordinates",
                DescribeRole.Theorem,
                Text("For lattice data, a charge, a chart, a real chart argument and a finite support "
                    + "containing every assigned mode, the native covariance is the submatrix of the "
                    + "compact covariance indexed by the tagged mode map on both sides. The native "
                    + "mean is the compact mean composed with that map.")),
            D("four-m-compact-word-readout", "compactWordReadout", "Compact word evaluation",
                DescribeRole.Definition,
                Text("Evaluate the compact affine coefficient at the four occupations of the "
                    + "mapped word and multiply by their four factorial weights.")),
            D("four-m-compact-ab-symmetry", "compactCovariance_ab_symm",
                "Symmetry in the radial slit charts", DescribeRole.Theorem,
                Text("In A or B, at a real argument whose complex chart parameter has norm less "
                    + "than one, the two compact covariance entries with interchanged indices are equal.")),
            D("four-m-compact-d-symmetry", "compactCovariance_d_symm",
                "Symmetry at the true D lip", DescribeRole.Theorem,
                Text("For a real argument strictly between zero and one, the true D-lip compact "
                    + "covariance entries with interchanged indices are equal. Continue the slit entry "
                    + "symmetry from the radial disk and take the one-sided limit at the reciprocal "
                    + "of the chart argument.")),
            D("four-m-compact-charge-term", "compactChargeTerm", "Compact charge summand",
                DescribeRole.Definition,
                Text("In the upper chart selection keep the period normalization, charge "
                    + "exponential, correction contractions and lifted scales of the physical "
                    + "partition sum. Read each surviving assignment by its four compact "
                    + "occupations and the actual signed covariance and charge-linear mean.")),
            D("four-m-compact-fourier-overlap", "compact_fourier_overlap",
                "Rank-24 signed Fourier overlap in compact occupations", DescribeRole.Theorem,
                Text("Let the lattice have rank 24, unit Gram determinant and positive definite "
                    + "real Gram form. Fix a real argument strictly between zero and one and an "
                    + "A-parameter square root of norm less than one. Take any word of distinct "
                    + "labels from a finite decidable type, with puncture, colour and spatial "
                    + "degree assigned to each label and a finite support containing all assigned "
                    + "modes. The charge terms of every chart are absolutely summable on every "
                    + "mod-two charge fibre. Write V for the resulting chart and class sums. "
                    + "For any class a, V(D,a) is 2⁻¹² times the sum of V(A,b) with Fourier sign "
                    + "at (a,b). V(B,a) is the corresponding sum with the extra quadratic sign "
                    + "of b and the inverse twelfth power of the A period root. Use the true D "
                    + "lip and the upper chart selection throughout. The proof replaces each "
                    + "surviving word using "),
                Ref(FourPoint + "OriginalFourMNativeOccurrenceReadout.native_occurrence_readout"),
                Text(" before applying "),
                Ref(FourPoint + "OriginalFourMAssignedOverlap.assigned_fourier_overlap"),
                Text(".")))));

    private static DocumentBlock D(string id, string name, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
