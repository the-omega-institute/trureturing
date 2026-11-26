using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuAlignedCubicOrbitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuAlignedCubicOrbit.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed CAR trace interpolation yields Wu’s cubic bound on aligned positive semidefinite fibers.",
        H("Aligned cubic orbit under physical odd-sector rotations"),
        Blocks(
            Describe.Lean(DescribeId.Create("directed-mixed-traces-affine"),
                DeclarationHandle.Create(Owner + "directed_mixed_traces_affine"),
                H("Affine interpolation of both directed mixed traces"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Use the physical odd basis (01, 10) and let a complex unitary U act on " +
                        "the even basis (00, 11). Write a, c, and k for the real even, odd, and cross entries " +
                        "of a datum. Its even, odd, and upper cross blocks are U diag(a) Uᴴ, diag(c), and " +
                        "U diag(k), with the adjoint lower cross block. For independent data M and N, use " +
                        "the same U for both matrices. Conjugate both by the physical exterior action of any odd " +
                        "unitary V. This action fixes the vacuum, acts by V on (01, 10), and acts by " +
                        "det V on the filled state. In the literal jump coordinates the maps are " +
                        "Φ(M) = ∑ₖ Jₖ M Jₖ* and Ψ(M) = ∑ₖ Jₖ* M Jₖ. Each directed real trace pairing " +
                        "equals the average of its unrotated endpoint values with " +
                        "weights p = |U₀₀|² and 1 − p. At z = det U, the endpoints are " +
                        "diag(1, z) and the matrix with rows (0, −z) and (1, 0)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-inequality-rotated-aligned"),
                DeclarationHandle.Create(Owner + "cubic_inequality_rotated_aligned"),
                H("Wu’s cubic inequality for physically rotated aligned fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Take exponent three in Wu v1, Remark 3.15, equations (3.54)–(3.55), " +
                        "for the two signed modes with common Gibbs odds r³ and r ≥ 1. Let D be the product " +
                        "Gibbs density, G = D^(1/6), and M = GXG. Assume M is a physical exterior rotation of the aligned " +
                        "matrix of two real symmetric positive semidefinite fibers, including singular ones. " +
                        "With t = Re Tr(M³), the Wick Dirichlet term (9/8) Re Tr(M² G ℒᵣ(X) G) " +
                        "bounds α(r)[Re Tr(M³(log M³ − log D)) − t log t]. The logarithms use the real " +
                        "functional calculus with Real.log 0 = 0.")),
                    Paragraph(Text("In occupation order (00, 01, 10, 11), put P = diag(1, −1, −1, 1), " +
                        "Kₖ = JₖP, and nₖ = Jₖ*Jₖ. The direct Wick generator uses the dissipators of Kₖ and Kₖ* " +
                        "at rates 2a and 2b, where a + b = 1 and b/a = r³. For j ≠ k, Kₖ and Kₖ* commute " +
                        "with the other mode’s local factors. The kth dissipator pair acts on I, Jₖ, Jₖ*, " +
                        "and nₖ − bI with eigenvalues 0, 1, 1, and 2. On the off-diagonal factors the " +
                        "rates add to a + b, and on the centered occupation the result is " +
                        "2a nₖ − 2b(I − nₖ) = 2(nₖ − bI). This is the one-mode action of Wu’s (3.2). " +
                        "The ordered products are Wu’s §3.3 Wick basis up to local scalar factors. " +
                        "In Wu’s convention γₖ is proportional to Jₖ*, so the centered vacuum projection " +
                        "is proportional to −(nₖ − bI). The ordered products have the sum of the local degrees.")),
                    Paragraph(Text("The diagonal unitary W = diag(1, i, i, 1) sends Jₖ to iKₖ by conjugation. " +
                        "The phase cancels in each dissipator, so conjugation intertwines the literal " +
                        "and Wick generators. It fixes D and G. The inverse conjugation phases the upper " +
                        "cross block by i and leaves the even block fixed, which replaces U by iU with " +
                        "the same positive semidefinite fibers. It commutes with the exterior action of V. " +
                        "Trace and functional calculus then transport the literal cubic bound to the Wick generator.")),
                    Paragraph(Text("At fixed even determinant, the aligned deficit is the same affine average of " +
                        "the endpoint deficits in the literal jump coordinates. The spectral trace terms " +
                        "are frame independent, and the Gibbs and jump-projection terms use affine diagonal " +
                        "moments. At the endpoints " +
                        "the matrices preserve the first and second occupations, respectively. The " +
                        "occupation-conditioned bound applies to both, using the graded swap for the second."))),
                DescribeRole.Theorem))));
}
