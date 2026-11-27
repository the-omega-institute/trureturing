using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibPositiveRationalPurityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic criterion for rational pure Fibonacci extensions with positive middle occupation.",
        H("Rational purity at positive middle occupation"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-positive-rational-purity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/FibPositiveRationalPurity.positive_rational_purity_iff"),
                H("The hidden coupling and its norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the edge data are rational and admit a pure common extension "
                        + "at positive middle occupation. If either coupling to a singly "
                        + "occupied endpoint is nonzero, that edge data force the hidden "
                        + "coupling to be rational. The pure extension then has rational entries.")),
                    Paragraph(Text(
                        "If both couplings vanish, the marginal equations constrain only the "
                        + "squared modulus of the hidden coupling. It equals the middle "
                        + "occupation times the occupied diagonal entry of the left endpoint "
                        + "block. A rational pure extension exists exactly when that number "
                        + "is a sum of two rational squares."))),
                DescribeRole.Theorem))));
}
