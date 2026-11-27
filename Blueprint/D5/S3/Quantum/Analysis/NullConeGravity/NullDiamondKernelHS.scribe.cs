using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondKernelHSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded integral operators, their adjoints, and the Hilbert–Schmidt estimate.",
        H("Square-integrable kernels on complex L²"),
        Blocks(
            Entry("integral-operator", "integralKernelOp", "Integral operator",
                "On an s-finite measure space, a square-integrable complex kernel defines a bounded "
                + "linear operator on complex L².", DescribeRole.Definition),
            Entry("section-formula", "integralKernelOp_ae", "Section integral",
                "For each vector f in L², the output at almost every x is the integral of K(x,y) f(y) in y."),
            Entry("operator-norm", "integralKernelOp_norm_le", "Operator norm estimate",
                "The operator norm is bounded by the L² norm of the kernel. Apply Cauchy–Schwarz "
                + "in each section and integrate the square of that bound."),
            Entry("operator-pairing", "integralKernelOp_inner", "Product integral for the pairing",
                "The inner product of f with the operator applied to g is the product integral of "
                + "the conjugate of f(x) times K(x,y) times g(y). The product belongs to L¹ "
                + "by Cauchy–Schwarz on the product space."),
            Entry("kernel-congruence", "integralKernelOp_congr_ae", "Independence of the representative",
                "Kernels that agree almost everywhere for the product measure induce the same operator."),
            Entry("operator-adjoint", "integralKernelOp_adjoint", "Adjoint kernel",
                "The adjoint is the integral operator with the conjugate transposed kernel. "
                + "Exchange the product coordinates in the pairing."),
            Entry("multiplier", "mulOp", "Bounded multiplication",
                "An essentially bounded complex function acts on L² by multiplication.", DescribeRole.Definition),
            Entry("multiplier-formula", "mulOp_ae", "Pointwise multiplication",
                "The multiplier output agrees almost everywhere with the pointwise product."),
            Entry("weighted-kernel", "integralKernelOp_mulOp_both", "Left and right multipliers",
                "Composing the kernel operator with a left multiplier g and a right multiplier h "
                + "gives the kernel g(x) K(x,y) h(y), which is again square integrable."),
            Entry("hilbert-schmidt", "integralKernelOp_hilbertSchmidt", "Hilbert–Schmidt membership",
                "For each finite set of basis vectors, apply Bessel's inequality to the conjugate kernel "
                + "section. Integrate this finite sum to bound it uniformly and obtain summability."),
            Entry("squared-norm", "integralKernelOp_hsSq_le", "Squared Hilbert–Schmidt norm estimate",
                "The squared Hilbert–Schmidt norm is at most the integral of the squared kernel norm "
                + "on the product space. This connects the square integrability of a kernel to "
                + "the operator estimate used for Eq. (71) of Satishchandran and Sorce."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
