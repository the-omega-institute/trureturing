using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.SharpWeightedLin;

internal sealed class SharpWeightedLinSettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.";
    private static readonly LibraryNoteRef Hiai = LibraryNoteRef.Create("D5/L/Divergence/hiai2025quasiarithmetic");
    private static readonly LibraryNoteRef Sra = LibraryNoteRef.Create("D5/L/Divergence/sra2026linconj");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp weighted Lin comparison", H("Sharp weighted Lin comparison"), Blocks([
            Describe.Lean(DescribeId.Create("hiai-arithmetic-mean"),
                DeclarationHandle.Create(Prefix + "hiaiArithmeticMean"),
                H("Weighted arithmetic power mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Hiai),
                Blocks(Paragraph(Text("For positive parameters and positive definite inputs, this is the spectral one over q power of the weighted sum of the q powers of A and B, as in Hiai Section 2.1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hiai-r-mean"),
                DeclarationHandle.Create(Prefix + "hiaiRMean"),
                H("Weighted sandwich power mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Hiai),
                Blocks(Paragraph(Text("This is the spectral one over p power of A to the power (one minus alpha) p over two, times B to the power alpha p, times the same A power. It is Hiai quasi-Renyi mean from Section 2.1, used in Section 4.3."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Sharp weighted spectral comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Hiai, Sra),
                Blocks(Paragraph(Text("For every dimension, weight strictly between zero and one, positive p, and q at least alpha times one minus alpha times p, every descending eigenvalue of the sandwich power mean is at most the corresponding eigenvalue of the arithmetic power mean on positive definite complex inputs. Sra inertia method is reused: inverse congruence gives a rank reduction, Schur inertia turns the spectral threshold into a nonpositive compressed quadratic form, and finite spectral measures reduce that form to the sharp scalar barrier x to the power a over b times (one minus a x) at most b. Equality holds at x equal to one. With a plus b equal to one, this gives the singular value endpoint exponent two a b; homogeneity and monotonicity of arithmetic power means give the stated range. At equal weights the endpoint is Sra and Drury exponent one half. Hiai Problem 4.15 and its necessary parameter bound are the source question; the endpoint sufficiency is the repository conclusion. Weak majorization and trace consequences by summation, source necessity, the remaining source trace region q at least one, and extension to semidefinite inputs by continuity are described separately in the problem dossier; they are not additional Lean conclusions here."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hiai-2025-problem-4-15-sharp-weighted-lin"),
                    ResolutionKind.Proved))])));
}
