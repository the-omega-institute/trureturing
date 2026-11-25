using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class NativeDetectorTranslationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Divided Source Translation for the Native Corrected-Field Detector",
        H("Divided Source Translation for the Native Corrected-Field Detector"),
        Blocks(
            Paragraph(Text("Let D be even integral lattice data with unit Gram determinant, witnessed by hu. "
                + "Take arbitrary actual twisted tensors R and S in ActualTensor D hu, and a source a in "
                + "Carrier D. Write T for LatticeSugawaraConformal.translation D and B_e(a) for the "
                + "detector with input R and test tensor S at signed doubled Hahn exponent e.")),
            Entry("native-detector", "detector", "The corrected-field detector",
                "Extract coefficient e of the original corrected field of a, apply it to R, and pair "
                + "the result with S using ActualChargedAdjoint.actualForm. The resulting functional "
                + "is complex-linear in a.",
                DescribeRole.Definition),
            Entry("native-detector-apply", "detector_apply", "Evaluation of the detector",
                "The value B_e(a) is actualForm D hu ((correctedField D hu a).coeff e R) S. "
                + "The field coefficient acts on the first tensor and the bilinear form tests it against the second."),
            Entry("native-detector-divided-translation", "detector_divided_translation",
                "Divided translation at every signed doubled exponent",
                "For every integer e and natural h, B_(e − 2h)(T^h a) divided by h! equals "
                + "binom(e/2, h) B_e(a), with the generalized binomial Ring.choose over the complex numbers. "
                + "LatticeHalfFockOriginalTranslation.correctedField_translation_physical gives "
                + "B_j(Ta) = ((j + 2)/2) B_(j + 2)(a) by bilinearity. Induction on h gives the "
                + "falling product of e/2 − k over 0 ≤ k < h. This is the coefficient identity "
                + "(1/h!) ∂_z^h z^(e/2) = binom(e/2, h) z^(e/2 − h) for formal half-integer powers. "
                + "The complex binomial normalization follows from Ring.choose_eq_smul and "
                + "descPochhammer_eval_eq_prod_range."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
