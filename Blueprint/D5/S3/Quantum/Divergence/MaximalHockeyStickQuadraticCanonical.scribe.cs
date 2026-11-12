using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticCanonicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual spectral reverse test attains the quadratic minimum and has an exact hockey profile.",
        H("The actual canonical spectral test"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-canonical-spectral-profile"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical."
                        + "quadratic_reverse_test_attained_profile"),
                H("Attainment and all thresholds for one test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite pair of positive semidefinite complex matrices, "
                        + "one actual test with card(n) labels attains quadraticValue. "
                        + "For S=A+B and C=normalize(S,A), its hockey profile equals "
                        + "Tr A - Re Tr(S canonicalOverlap(C,t)) for every real t. "
                        + "Both assertions come from the spectral preparation itself. "
                        + "There is no inference from cost equality alone, and there are "
                        + "no faithfulness, nonzero or nonempty-carrier hypotheses."))),
                DescribeRole.Theorem))));
}
