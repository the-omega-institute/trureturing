using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricActualOcticWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cut-free theorem for an arbitrary actual octic window.",
        H("Actual octic windows with scalar multiplication idealizer"),
        Blocks(
            Paragraph(Text(
                "F has characteristic zero, D/F is an arbitrary extension of degree eight, and W is an "
                + "arbitrary four dimensional F subspace of D. Its multiplication idealizer is exactly F. "
                + "Q(W) consists of u/v with u and v in W and v nonzero; since W is nonzero this includes zero. "
                + "K/F is any finite normal extension containing this same D, including its normal closure. "
                + "Omega is the literal type of all F algebra embeddings D to K.")),
            Describe.Lean(
                DescribeId.Create("actual-general43-2-cut-free"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/AuricActualOcticWindow.general43_2_cut_free"),
                H("The original actual cut-free clause"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a outside Q(W), A(a) is multiplication by a on W followed by D/W. "
                        + "A nonzero kernel vector would exhibit a as a quotient of two elements of W, "
                        + "so A(a) is injective; both spaces have dimension four, hence it is invertible. "
                        + "The original operator is n = inclusion composed with A(a) inverse and the quotient map. "
                        + "The canonical K algebra splitting sends c tensor d to the function sigma maps to "
                        + "c times sigma(d). Under this splitting, the scalar extension of n has square zero "
                        + "and has image and kernel exactly the image of K tensor W. Its actual matrix N has "
                        + "square zero, rank four, and the covariance N(g sigma,g tau) = g(N(sigma,tau)).")),
                    Paragraph(Text(
                        "Write rho(S) for the dimension of the projection of this actual split window onto S. "
                        + "Coefficient extraction along an F basis of K shows that a tensor preserving the "
                        + "window has every coefficient in the original multiplication idealizer. Consequently "
                        + "every diagonal stabilizer of the split window is scalar. Equality in the complementary "
                        + "projection dimension bound would give a nonconstant indicator stabilizer, so the row "
                        + "rank is connected. The actual Galois action is transitive on Omega and preserves rho. "
                        + "Applying the existing fractional submodular cover theorem to the orbit of S gives "
                        + "2 rho(S) at least the cardinality of S. For the nonnegative submodular defect "
                        + "2 rho(S) minus the cardinality of S, a minimal nonempty zero set has translates "
                        + "which cannot cross a zero set. Their union proves that the complement of a zero set "
                        + "is zero. Connectivity excludes this equality for every nonempty proper S. Thus "
                        + "2 rho(S) is at least the cardinality of S plus one, derived from the same actual W.")),
                    Paragraph(Text(
                        "Rank-nullity applied twice to n restricted to the complementary coordinate space gives "
                        + "2 rho(S) at most the cardinality of S plus rank N[S,S complement]. If both crossing "
                        + "ranks were at most one for a cut of size two through six, strict rank forces a triple C "
                        + "with rho(C)=2 and rho(C complement)=3. Two conjugate triples cannot meet in two points, "
                        + "by submodularity on the triples and strict rank on their intersection and union. They "
                        + "cannot meet in one point, by applying the same argument to one triple and the complement "
                        + "of the other. Distinct conjugate triples are therefore disjoint. Transitivity would "
                        + "partition eight labels into triples, a contradiction. Hence at least one actual crossing "
                        + "block has rank at least two. This is the cut-free clause of the existing source argument; "
                        + "the full classification remains open. No mathematical novelty is claimed."))),
                DescribeRole.Theorem))));
}
