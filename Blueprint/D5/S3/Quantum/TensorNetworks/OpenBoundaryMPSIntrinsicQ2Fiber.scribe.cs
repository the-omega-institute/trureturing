using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSIntrinsicQ2FiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSIntrinsicQ2Fiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic actual-image Q2 fibers from observable quotient retraction.",
        H("Raw prefix nonidentifiability in the actual MPS image"),
        Blocks(
            Item("intrinsic-actual", "intrinsic_actual_q2_fiber", "Intrinsic actual-image Q2 nonidentifiability",
                "For every m, one nonzero real polynomial in the complete raw Q3 entries defines a nonempty relatively open dense locus inside the literal actual image of length 3+m binary bond-two free-boundary states. At every state in this locus and in every relative neighborhood, there is an actual state with equal complete raw Q2 and no unit-complex phase relation. The proof descends the twelve-component polynomial record through the quotient rational retraction, clears the coordinate-specific denominators, and multiplies by the quotient-locus and leading-block factors so the rank fiber remains inside the valid retraction and Schur-completion region.",
                DescribeRole.Theorem,
                "This is the intrinsic endpoint for the displayed raw PREFIX reading. It does not assert arbitrary interior windows, normalized readings, dynamics, energy, clocks, thermodynamics, stability or sample complexity, and it does not claim solved-open-problem credit for the broader Critch–Morton Conjecture 9 source quantifier."),
            Item("quotient-validity-open", "quotientValidityDomain_open", "Open canonical quotient validity domain",
                "The original quotient domain is open in REAL13: sigma is positive, the actual prefix-Q3 quotient locus polynomial is nonzero, and the leading polynomial is nonzero. This original proof is exposed for the finite-product actual witness construction in InteriorSpectralAmbiguity.observed_interior_ambiguity.", DescribeRole.Lemma),
            Item("quotient-validity-nonempty", "quotientValidityDomain_nonempty", "Actual witness for the quotient validity domain",
                "The original canonical positive witness lies in this domain for every m, including m=0. The observed interior ambiguity consumer intersects this domain with the dense nonzero locus of the product of REAL13 certificates. The original quotientNumeratorFamily and quotientDenominatorFamily are exposed unchanged for the same clearing construction.", DescribeRole.Lemma),
            Paragraph(Text("The canonical core and phase argument retain Haobo Ma and Wenlin Zhang's CC BY 4.0 attribution through OpenBoundaryMPSTwoSiteMinimality. The local C1 supplier credits BochaoKong's Apache-2.0 LeanPool argument at commit 2b1ec889365345f19a45fa94b6457a4d92c96295. The foundational polynomial observations and actualPrincipalLocus/actual_principal_genericity API belong to OpenBoundaryMPSQ2PolynomialFiber.")),
            Paragraph(Text("The interior-genericity consumer uses quotientRawPrefix, positiveRepresentative_witness, quotientCoordinates_retraction_local, quotientCoordinates_positiveRepresentative and rawPrefix_scale_local.")))));

    private static DocumentBlock Item(string id, string selector, string title, string text,
        DescribeRole role, params string[] continuation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(text)), .. continuation.Select(s => Paragraph(Text(s)))]), role);
}
