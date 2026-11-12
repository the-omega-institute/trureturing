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
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text(
                    "For every finite pair of positive semidefinite complex matrices, "
                        + "one actual test with card(n) labels attains quadraticValue. "
                        + "For S=A+B and C=normalize(S,A), its hockey profile equals "
                        + "Tr A - Re Tr(S canonicalOverlap(C,t)) for every real t. "
                        + "Both assertions come from the spectral preparation itself. "
                        + "There is no inference from cost equality alone, and there are "
                        + "no faithfulness, nonzero or nonempty-carrier hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadraticcanonical-quadratic-reverse-test-attained"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained"),
                H("The attained quadratic cost projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For every finite PSD A,B, an actual ReverseTest with card(n) labels attains quadraticValue A B. This is the cost projection of the same all-threshold spectral test. Hiai canonical spectral and quadratic optimality are known antecedents; this finite source statement retains singular, zero and empty cases."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadraticcanonical-maximal-quadratic-eq-value"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.maximal_quadratic_eq_value"),
                H("The genuine finite quadratic infimum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For every finite PSD A,B, maximalQuadratic A B equals the EReal embedding of quadraticValue A B. The universal lower bound and the actual attained spectral test sandwich the defining all-k infimum. QuadraticEquality uses the exact finite value. This realizes known quadratic optimality and asserts no general-convex attainment theorem."))), DescribeRole.Theorem))));
}
