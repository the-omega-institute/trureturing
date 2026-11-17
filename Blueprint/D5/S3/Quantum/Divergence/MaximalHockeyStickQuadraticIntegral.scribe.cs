using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite triangle integral represents the standard quadratic closed perspective and actual test cost.",
        H("The bounded quadratic hockey reference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-star-perspective-integral"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral."
                        + "star_perspective_hockey_integral"),
                H("Exact scalar reference, including both axes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text(
                    "For p,q >= 0, the standard perspective (p-q)^2/(p+q), with value "
                        + "zero at the origin, is q-3p plus eight times the integral of "
                        + "max(p-u(p+q),0) over 0 <= u <= 1. The proof integrates the "
                        + "linear triangle up to p/(p+q) and treats p=q=0 separately. "
                        + "This is the closed perspective of f_*(s)=(s-1)^2/(s+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-star-actual-cost-integral"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral."
                        + "star_cost_hockey_integral"),
                H("The actual reverse-test cost identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text(
                    "Summing the scalar identity over the actual finite labels gives "
                        + "starCost = Tr B - 3 Tr A + 8 integral compactHockey. "
                        + "For 0<u<1, compactHockey is exactly (1-u) times the original "
                        + "classical hockey profile at t=u/(1-u). No improper integral "
                        + "or unproved identification with another cost is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadraticintegral-compacthockey"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compactHockey"),
                H("The actual compact-coordinate classical profile"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("compactHockey R u is sum max(p_i-u(p_i+q_i),0) over the original labels of R, for every real u. It is the bounded-interval profile integrated in the exact quadratic cost formula."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadraticintegral-compact-hockey-continuous"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_continuous"),
                H("Continuity on the entire real line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For any actual finite test, compactHockey R is continuous on all real u. It is a finite sum of maxima of affine functions. QuadraticEquality uses this continuity to detect a nonzero gap on a neighbourhood."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-quadraticintegral-compact-hockey-eq-scaled"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_eq_scaled"),
                H("Exact return to positive thresholds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For an actual finite test and 0<u<1, compactHockey R u=(1-u) hockey R (u/(1-u)). The proof factors the positive coefficient 1-u through each positive part. QuadraticEquality transports the compact gap to the original positive-threshold profile with this identity."))), DescribeRole.Theorem))));
}
