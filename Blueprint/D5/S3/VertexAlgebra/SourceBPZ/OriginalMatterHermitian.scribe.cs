using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class OriginalMatterHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal frame-free original matter Hermitian supplier on the existing charge and oscillator carrier.",
        H("Original Matter Hermitian Form and Adjoint Modes"),
        Blocks(
            Paragraph(Text("The carrier, source Wick pairing, coefficient conjugation kappa, source reflection theta and original integer currents are the existing definitions. Hm is the literal sourcePairing D (theta D (kappaCarrier x)) y, with no transverse frame, positive metric or desired-result premise. The Gram remains the original indefinite symmetric integral Gram.")),
            Paragraph(Text("The current adjoint is proved for every integer mode m, including zero and the signs plus or minus one. normalSummand_adjoint retains the literal k<0 and k>=0 branches and the k=0 reversal. Hm_sugawaraMode uses both inverse hypotheses for H * gramComplex D and gramComplex D * H, and derives the coefficient conjugation and transpose identities.")),
            Paragraph(Text("This source currently has no Reg registration mirror. The exact public declaration inventory, statement identities, type hashes and standard axiom bindings are retained for the unfinished audit in https://github.com/the-omega-institute/trureturing/issues/25777; reconstruction, actual bridge, family-variation and sensitivity certificates remain open. The complete Monster/VOA/CFT/string/AdS objective remains unfinished.")),
            Node("kappaOsc", "Coefficient conjugation on oscillators", "Maps polynomial coefficients by complex conjugation and fixes the original oscillator variables.", DescribeRole.Definition),
            Node("kappaCarrier", "Coefficient conjugation on the carrier", "Applies kappaOsc on each existing finite-charge oscillator component.", DescribeRole.Definition),
            Node("kappaOsc_pderiv", "Conjugation commutes with pderiv", "The original coefficient conjugation commutes with every oscillator partial derivative.", DescribeRole.Theorem),
            Node("kappaOsc_annihilate", "Conjugation commutes with annihilation", "The actual Gram-weighted annihilation operator is preserved under coefficient conjugation.", DescribeRole.Theorem),
            Node("kappaOsc_neutralPolynomialMode", "Conjugation commutes with every polynomial mode", "The negative, zero and positive original integer mode branches are preserved by kappaOsc.", DescribeRole.Theorem),
            Node("kappaCarrier_neutralMode", "Conjugation commutes with every carrier mode", "The carrier lift intertwines each original neutral current at every integer frequency.", DescribeRole.Theorem),
            Node("kappaOsc_involutive", "Oscillator conjugation is involutive", "Applying the coefficient conjugation twice returns the original oscillator.", DescribeRole.Theorem),
            Node("integerWick_kappa", "Conjugation of the source Wick pairing", "The actual retuned signed Wick pairing conjugates under kappaOsc in both slots.", DescribeRole.Theorem),
            Node("kappaOsc_sigma", "Conjugation and oscillator reflection", "The original sigma reflection commutes with coefficient conjugation.", DescribeRole.Theorem),
            Node("kappaCarrier_theta", "Conjugation and source reflection", "The carrier coefficient conjugation commutes with the existing source theta.", DescribeRole.Theorem),
            Node("sourcePairing_kappa", "Conjugation of the source pairing", "The finite opposite-charge source pairing conjugates under kappaCarrier in both inputs.", DescribeRole.Theorem),
            Node("conjugateH_eq_H", "Inverse Gram conjugation symmetry", "Under both inverse hypotheses, the matrix H is fixed by entrywise complex conjugation.", DescribeRole.Theorem),
            Node("transposeH_eq_H", "Inverse Gram transpose symmetry", "Under both inverse hypotheses, the matrix H is fixed by transpose using the original symmetric Gram.", DescribeRole.Theorem),
            Node("kappaCarrier_involutive", "Carrier conjugation is involutive", "Applying kappaCarrier twice returns every original carrier state.", DescribeRole.Theorem),
            Node("theta_square", "Source reflection is involutive", "The existing source theta squares to the identity on the carrier.", DescribeRole.Theorem),
            Node("Hm", "Literal frame-free Hermitian form", "Defines Hm x y as sourcePairing D (theta D (kappaCarrier x)) y on the original carrier.", DescribeRole.Definition),
            Node("Hm_alt", "Reflected second-slot form", "Rewrites Hm by moving the existing source reflection to the second input.", DescribeRole.Theorem),
            Node("Hm_hermitian", "Hermitian symmetry", "The literal source form satisfies Hm x y = conj (Hm y x).", DescribeRole.Theorem),
            Node("Hm_neutralMode", "All-integer current adjoint", "For every index and every integer m, neutralMode at m in the first slot transposes to neutralMode at -m in the second slot.", DescribeRole.Theorem),
            Node("Hm_neutralMode_comp", "Composed current adjoint", "Two original neutral modes transpose with reversed order and negated integer frequencies.", DescribeRole.Theorem),
            Node("normalSummand_adjoint", "Normal summand adjoint", "The literal normalSummand branches k<0 and k>=0 transpose to the reversed pair with negated frequencies, including the k=0 reversal.", DescribeRole.Theorem),
            Node("Hm_add_left", "Additivity in the first slot", "Hm is additive in its first carrier input.", DescribeRole.Theorem),
            Node("Hm_add_right", "Additivity in the second slot", "Hm is additive in its second carrier input.", DescribeRole.Theorem),
            Node("Hm_smul_left", "Conjugate scalar action in the first slot", "A scalar in the first slot acts by its complex conjugate.", DescribeRole.Theorem),
            Node("Hm_smul_right", "Scalar action in the second slot", "A scalar in the second slot acts directly.", DescribeRole.Theorem),
            Node("Hm_sugawaraMode", "All-mode Sugawara adjoint", "For every integer m, the original matrix Sugawara mode at m transposes to the mode at -m under both inverse Gram hypotheses.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("original-matter-hermitian-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
