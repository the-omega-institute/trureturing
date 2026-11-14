using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.Hadamard;

internal sealed class BanicaTruncationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/banicaoztekepittau2018isolated");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier truncation, analytic phase curves and the real-density isolation assertion.",
        H("Fourier truncation and phase deformations"),
        Blocks(
            Entry("partial-fourier", "partialFourier", "Partial Fourier matrices",
                "For positive p, the row set S is a finite subset of Z/pZ and every column is retained. " +
                "The (s,j) entry is exp(2 pi i val(s) val(j)/p).",
                DescribeRole.Definition, true),
            Entry("partial-hadamard", "IsPartialHadamard", "Partial Hadamard matrices",
                "In source Definition 1.1, every entry has complex norm one, and the Hermitian inner product of any two distinct rows is zero.",
                DescribeRole.Definition, true),
            Entry("deformation", "IsDeformation", "Analytic deformations",
                "This is the analytic specialization of source Definition 1.3: a globally real analytic matrix curve through H " +
                "whose values near zero are partial Hadamard matrices. " +
                "Use the local coordinate q = exp(i t), with q near 1 on the unit circle and real t near 0. " +
                "On the principal branch, q^alpha = exp(i alpha t) for real alpha. " +
                "Real analyticity implies continuous differentiability of every finite order.",
                DescribeRole.Definition, true),
            Entry("trivial-deformation", "IsTrivialDeformation", "Row and column phase deformations",
                "This generalizes the trivial deformations of source Definition 1.3: near zero, each entry is " +
                "H(s,j) exp(i (a(s,t)+b(j,t))), with no regularity required of the real phase functions. " +
                "In the local coordinate q = exp(i t), with q near 1 and t near 0, the principal branch gives q^alpha = exp(i alpha t). " +
                "Thus the source's f_ij(q)=H_ij q^{alpha_i+beta_j} is included by taking a_i(t)=t alpha_i and b_j(t)=t beta_j. " +
                "Source isolation implies isolation in this encoding, which tests analytic curves against a larger trivial class; " +
                "hence the encoded negation of the conjecture refutes the source conjecture.",
                DescribeRole.Definition, true),
            Entry("isolated", "IsolatedPartialHadamard", "Isolation",
                "This is the analytic specialization of isolation following source Definition 1.3: " +
                "every analytic deformation through H must agree near zero with row and column phase multiplication. The enlarged trivial class makes this isolation condition weaker than source isolation.",
                DescribeRole.Definition, true),
            Entry("claim", "claim", "The real-density truncation assertion",
                "In this analytic specialization of source Conjecture 1.14, there is a positive real epsilon such that, " +
                "for every prime p and every row set S with " +
                "cardinality at least (1-epsilon)p, the prescribed partial Fourier matrix is isolated.",
                DescribeRole.Definition, true),
            Entry("fourier-hadamard", "partial_fourier_isPartialHadamard", "Fourier orthogonality",
                "The prescribed exponential Fourier entries agree with the standard additive character. " +
                "The character has unit modulus, and its nonzero-frequency sums vanish, proving the partial Hadamard condition.",
                DescribeRole.Theorem),
            Entry("regular-tangent", "not_isolated_of_regular_tangent", "A nontrivial tangent produces a nontrivial curve",
                "Suppose the real phase Jacobian is surjective and has a kernel vector outside the additive row-column phase space. " +
                "An analytic regular-level curve realizes a positive multiple of that vector. For nonempty row and column sets, " +
                "triviality forces equality of the two cross-products of phase exponentials at each parameter. " +
                "Differentiating these smooth cross-products at zero makes every tangent cross-difference vanish, " +
                "putting the tangent inside the row-column space, a contradiction. The arbitrary trivial phase functions are never differentiated.",
                DescribeRole.Theorem),
            Entry("two-row-truncation", "two_row_truncation_not_isolated", "Deleting two rows",
                "For every prime p at least five and every row set of cardinality p-2, the Fourier phase Jacobian is surjective. " +
                "Its kernel has dimension 3(p-2), exceeding the additive row-column parameter bound 2p-2. " +
                "A tangent outside that space therefore gives a nontrivial analytic matrix deformation.",
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The density assertion is false"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any positive real epsilon, choose a sufficiently large prime p and delete two rows. " +
                    "The remaining density is at least 1-epsilon, while the resulting partial Fourier matrix admits a nontrivial analytic deformation."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("banica-ozteke-pittau-2018-truncation-isolation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string selector, string title, string text,
        DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
        StatementSource.WithoutFormula(),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);
}
