using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class InvertibleHermitianInertiaPullbackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invertible square Hermitian congruence preserves the full finite inertia pair.",
        H("Invertible Hermitian Inertia Pullback"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invertible-hermitian-inertia-pullback"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det"),
                H("Invertible congruence preserves positive and negative index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive-index pullback monotonicity is applied in both directions through the nonsingular inverse; matrix negation transports the same argument to negative index. The theorem is finite-dimensional and assumes only an invertible square feature matrix."))),
                DescribeRole.Theorem)
        ),
        []));
}
