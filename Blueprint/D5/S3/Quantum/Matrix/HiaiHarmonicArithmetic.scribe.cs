using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HiaiHarmonicArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiai2025quasiarithmetic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Harmonic arithmetic mean parameter necessity", H("Harmonic arithmetic mean parameter necessity"), Blocks([
            Describe.Lean(DescribeId.Create("power-mean"),
                DeclarationHandle.Create(Prefix + "powerMean"),
                H("Quasi-arithmetic matrix mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a weight alpha strictly between zero and one and a nonzero real parameter t, this is the one over t power of the weighted sum of the t powers of A and B. Powers use continuous functional calculus. The theorem uses positive definite complex matrices, where this agrees with the spectral definition in Section 2.1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("harmonic-mean"),
                DeclarationHandle.Create(Prefix + "harmonicMean"),
                H("Quasi-harmonic matrix mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Raise A and B to p, take the inverse of the weighted sum of their inverses, and then take the one over p power. On positive definite matrices this equals the quasi-arithmetic mean with parameter minus p; the identity is proved in the module."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both parameters must be at least one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean conclusion concerns alpha strictly between zero and one, positive parameters p and q, and positive definite two by two complex matrices. If the quasi-harmonic mean with parameter p is below the quasi-arithmetic mean with parameter q in the Loewner order for every such pair, then p and q are both at least one. This answers Section 5 (4) of arXiv:2508.20309v2: together with the source sufficiency and the paper direct sum extension, it gives the complete characterization for alpha strictly between zero and one on positive semidefinite matrices in every dimension at least two. The real symmetric test family is embedded in complex matrices: A has eigenvalues one and x, while B has eigenvalues one and x squared and is rotated by an angle with squared sine z. Two-point functional calculus computes its power means. A derivative with respect to z at zero gives the determinant coefficient. For p below one the first term in the simplified coefficient tends to zero, while the magnitude of its negative term tends to the square of one minus alpha; the coefficient therefore tends to the negative square of one minus alpha. Positive semidefiniteness would force that coefficient to be nonnegative. Inverting both inputs and reversing the inverse order gives the necessity for q. The source sufficiency for parameters at least one, including its limiting definition of the harmonic mean on singular inputs, is not formalized here. The positive definite counterexamples already belong to the positive semidefinite domain; their extension by a common identity block is a paper consequence, not an additional Lean conclusion. At alpha zero or one both means equal the same input for all positive parameters, and in dimension one the scalar comparison holds for all positive parameters; these statements are also not formalized here."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hiai-2025-harmonic-arithmetic-mean-necessity"),
                    ResolutionKind.Proved))])));
}
