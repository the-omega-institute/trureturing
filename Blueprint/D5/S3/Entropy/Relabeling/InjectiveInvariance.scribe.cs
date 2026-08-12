using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Relabeling;

internal sealed class InjectiveInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete Shannon entropy is invariant under injective relabeling of the support.",
        H("Shannon Entropy Is Invariant Under Injective Relabeling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shannon-entropy-injective-invariance"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Relabeling/InjectiveInvariance.shannonEntropy_extend_injective"),
                H("Shannon entropy is unchanged by injective relabeling"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Sp, Eq, Sp,
                    F.Id("H"), Open, F.Id("X"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an injective map f : iota -> kappa and arbitrary real weights p : iota -> R, "
                        + "the pushforward extend f p 0 — equal to p on the image of f and 0 off it — has the "
                        + "same Shannon entropy as p: shannonEntropy (extend f p 0) = shannonEntropy p. This "
                        + "is the discrete-entropy-column identity H(f(X)) = H(X) for f injective on the "
                        + "support. The relabeling is by an embedding (injective, into a possibly-larger "
                        + "index type), not merely a bijection or permutation; padding with 0 off the image "
                        + "leaves the entropy unchanged because injectivity preserves the multiset of "
                        + "probabilities and negMulLog 0 = 0. Here shannonEntropy is the negMulLog sum "
                        + "-sum p_i ln p_i (entropy in nats). The identity holds for arbitrary real weights, "
                        + "so probability distributions are the special case, and it generalises the "
                        + "coordinate-swap invariance of joint entropy already in the entropy domain.")),
                    Paragraph(Text(
                        "The proof rewrites the iota-indexed sum through f on the image Finset.univ.image f "
                        + "(injectivity, via Finset.sum_image), then extends to the full index type kappa by "
                        + "Finset.sum_subset: the off-image terms vanish since extend gives the pad value 0 "
                        + "and negMulLog 0 = 0.")),
                    Paragraph(Text(
                        "Only the injective-invariance equality is recorded. The strict-decrease remark — "
                        + "that a non-injective f which merges positive-mass atoms strictly decreases the "
                        + "entropy — is not covered by this statement."))),
                DescribeRole.Theorem))));
}
