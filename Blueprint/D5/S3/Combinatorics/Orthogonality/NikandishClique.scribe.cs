using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class NikandishCliqueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/NikandishClique.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/nikandish2026orthogonality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact clique number for all nonzero binary subspaces in every positive dimension.",
        H("Nikandish's subspace orthogonality clique number"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orthogonality-graph"),
                DeclarationHandle.Create(Prefix + "orthogonalityGraph"),
                H("The source graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Vertices are all nonzero subspaces of F_2^n. Distinct U and W are adjacent "
                    + "exactly when sum_i u_i w_i is zero for every u in U and w in W. "
                    + "There is no dimension, nondegeneracy, or intersection restriction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonzero-subspace-count"),
                DeclarationHandle.Create(Prefix + "nonzeroSubspaceCount"),
                H("An independent lattice count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "N(r) is the natural cardinality of the complete nonzero submodule lattice "
                    + "of Fin r -> ZMod 2. In particular N(0)=0. No Gaussian-binomial bridge "
                    + "is asserted by this definition or by the result."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-clique-number"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact formula in every dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n with 1 <= n, omega(O_n*) equals "
                        + "max(n, N(n/2) + n%2), using natural-number division and remainder. "
                        + "This is the literal all-subspace question in source Problem 4.2.")),
                    Paragraph(Text(
                        "For an arbitrary clique, sum the radicals of its members to obtain R. "
                        + "Every member U lies in R-perp and U intersect R equals rad(U). "
                        + "The restricted form descends to R-perp/R. Its nonzero member images "
                        + "have nondegenerate restrictions and are indexed independent, so "
                        + "their number is at most n-2 dim(R). The other members inject into "
                        + "the nonzero submodule lattice of R. No nonalternating hypothesis "
                        + "is imposed on the quotient.")),
                    Paragraph(Text(
                        "For r >= 1, a hyperplane embedding, one outside line, and the whole "
                        + "space give N(r+1) >= N(r)+2. This moves the upper bound to an endpoint. "
                        + "Coordinate lines attain n. Duplicating t coordinates gives a totally "
                        + "isotropic t-space whose full nonzero lattice attains N(t); in odd "
                        + "dimension its perpendicular space is a distinct extra vertex.")),
                    Paragraph(Text(
                        "The source already provides the odd construction at n=7. Its Lemma 3.2 "
                        + "incorrectly counts three nonzero subspaces of F_2^2; there are four. "
                        + "The present upper bound does not use that argument. Prior-resolution "
                        + "searches are bounded and do not certify worldwide novelty."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality"))
        ]));

    // Final publication requires the caller-owned Freeze followed by attaching to result:
    // new OpenProblemResolutionClaim(
    //     ProblemSlugRef.Create("nikandish-subspace-orthogonality-clique"), ResolutionKind.Proved).
}
