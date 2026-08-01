using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class DualCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/DualCharacterization",
            "Mirror fixed points and unitary half-density parameters define the same midline."),
        H("Dual Characterization of the Critical Midline"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-fixed-points-and-unitary-parameters-define-the-critical-midline"),
                DescribeKind.Theorem,
                H("Mirror fixed points and unitary parameters define the critical midline"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Midline/DualCharacterization.midline_dual_characterization")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For any additive ledger with at least one nonzero length, the set of "
                    + "conjugate-reflection fixed points equals both the set of parameters whose "
                    + "half-density readings all have unit norm and the line of parameters with "
                    + "real part one half. This set-level theorem is derived from the existing "
                    + "pointwise critical-line characterizations. It locates no zeta zero and "
                    + "asserts no Riemann-hypothesis conclusion."))),
                LatexStatement.Create(
                    @"$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ (\exists a,\ell(a)\neq 0) \Rightarrow "
                    + @"(\{s\in\mathbb{C}:\operatorname{mirror}(s)=s\}"
                    + @"=\{s\in\mathbb{C}:\forall a,\Vert\operatorname{halfDensityReading}(\ell,s,a)\Vert=1\}"
                    + @"\ \land\ \{s\in\mathbb{C}:\operatorname{mirror}(s)=s\}"
                    + @"=\{s\in\mathbb{C}:\Re(s)=\frac{1}{2}\})$$")))));
}
