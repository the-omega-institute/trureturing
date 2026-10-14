using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalAbsoluteGhostSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral number degree separates the actual finite native kappa-zero branches.",
        H("Actual Native Ghost Support"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-integral-support"),
                DeclarationHandle.Create(Prefix + "native_ghost_support"),
                H("Finite Coefficient Support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing nativeWord_J supplies the exact signed occupation eigenvalue. Applying the actual native coefficient map to the finite charge-sector expansion proves a diagonal coefficient equation. Integer cast injectivity and a nonzero actual coefficient force its degree to equal the degree of the original homogeneous state. This is a coefficient computation, not a spectral assumption on a transferred abstract equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absolute-down-relative"),
                DeclarationHandle.Create(Prefix + "ghost_one_projector_relative"),
                H("Degree One Eliminates The Up Branch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual P coefficient diagonal forces kappa zero. The existing kappa_zero_iff then leaves exactly empty ghost support of degree one or singleton-three support of degree two. Homogeneity one eliminates the latter. Applying original B(0) to the full finite native expansion proves it vanishes, without assuming B(0) of the input state is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("other-native-degrees-zero"),
                DeclarationHandle.Create(Prefix + "projector_other_ghost_vanishes"),
                H("All Other Integral Degrees Vanish"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every supported coefficient of a P-fixed homogeneous charge-sector state has degree one or two. For every other integer degree the actual finite expansion is zero. No occupation cutoff or finite model replaces the original carrier. The reused eigenword and projector applications have no independent novelty credit."))),
                DescribeRole.Theorem))));
}
