using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Mixing;

internal sealed class MixtureEntropyBracketDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite mixture entropy lies between weighted component entropy and that entropy plus the weight entropy; the upper equality case for pairwise disjoint supports is not covered in this stratum.",
        H("The Finite Mixture Entropy Bracket"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixture-is-the-weighted-component-law"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture"),
                H("A mixture is the weighted component law"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("m"), Open, F.Id("j"), Close, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Open, F.Id("j"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index carrier, the mixture mass at j is the sum of the " +
                        "component masses q_i(j), weighted by w(i). The definition itself does " +
                        "not impose normalization; the bracket theorems separately require w " +
                        "and every component to be probability laws."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixture-joint-law-selects-a-component"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint"),
                H("The mixture joint law selects a component"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("P"), Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Eq, Sp, F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Open, F.Id("j"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint law records both the selected component i and its output j. " +
                        "Its cell mass is w(i) q_i(j), which provides the common joint object " +
                        "used by the chain-rule and mutual-information arguments."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-mixture-joint-marginal-is-the-weight-law"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_marginal_eq_weight"),
                H("The first mixture-joint marginal is the weight law"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("P"), Close,
                    Eq, Sp, F.Id("w"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing the joint law over j gives w(i), because each component q_i " +
                        "has unit total mass. This identity does not require w to be normalized " +
                        "or nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-mixture-joint-marginal-is-the-mixture"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_swapped_marginal_eq_mixture"),
                H("The second mixture-joint marginal is the mixture"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Operatorname, Grp(F.Id("swap")), Open, F.Id("P"), Close, Close,
                    Eq, Sp, F.Id("m"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "After swapping the two coordinates, marginalization over i is " +
                        "definitionally the weighted mixture. No probability-law hypotheses " +
                        "are needed for this finite-sum identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixture-joint-conditional-entropy-is-weighted-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_conditionalEntropy_eq_weighted"),
                H("Mixture-joint conditional entropy is weighted entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("P"), Close,
                    Eq, Sp, Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Conditioning the joint law on i recovers q_i whenever w(i) is nonzero, " +
                        "so its conditional-entropy contribution is w(i) H(q_i). If w(i) is " +
                        "zero, both sides of that slice identity vanish. Thus no restriction to " +
                        "the support of w is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-component-entropy-is-below-mixture-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.weighted_entropy_le_mixture_entropy"),
                H("Weighted component entropy is below mixture entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close,
                    Leq, Sp, F.Id("H"), Open, F.Id("m"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For normalized nonnegative weights and normalized nonnegative " +
                        "components, conditioning the mixture joint law on its selector cannot " +
                        "have more entropy than the output marginal. Substituting the three " +
                        "joint identities gives the lower side of the mixture bracket."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixture-entropy-is-below-weighted-plus-weight-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_le_weighted_add_weight_entropy"),
                H("Mixture entropy is below weighted plus weight entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("m"), Close, Leq, Sp,
                    F.Id("H"), Open, F.Id("w"), Close, Plus, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The chain rule expresses joint entropy as H(w) plus weighted component " +
                        "entropy. Applying the chain rule after swapping coordinates expresses " +
                        "the same joint entropy as H(m) plus a nonnegative conditional term, " +
                        "which proves the upper side of the bracket.")),
                    Paragraph(Text(
                        "This stratum does not classify equality in this upper bound. In " +
                        "particular, the pairwise-disjoint-support characterization of the " +
                        "components is intentionally not claimed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixture-entropy-gain-is-mutual-information"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_sub_weighted_eq_mutual_information"),
                H("Mixture entropy gain is mutual information"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("m"), Close, Minus, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close,
                    Eq, Sp, F.Id("I"), Open, F.Id("P"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The entropy gained by forgetting the selector is exactly the mutual " +
                        "information between selector and output in the mixture joint law. The " +
                        "identity follows by combining the joint chain rule with the frozen " +
                        "entropy decomposition of finite mutual information."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bracket-equality-means-identical-active-components"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_eq_weighted_iff_components_eq"),
                H("Lower-bracket equality means identical active components"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("m"), Close, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close,
                    Sp, Leftrightarrow, RowBreak,
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Eq, Sp, F.Id("m"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality in the lower bracket is equivalent to zero mutual information " +
                        "for the mixture joint law. The finite independence characterization " +
                        "then says that the joint law is the product of its marginals. Cancelling " +
                        "each nonzero weight gives q_i = m, and the converse reconstructs the " +
                        "product law from those component equalities.")),
                    Paragraph(Text(
                        "Zero-weight components are deliberately excluded from the conclusion. " +
                        "They contribute neither joint mass nor weighted entropy and therefore " +
                        "may be arbitrary without affecting equality."))),
                DescribeRole.Theorem))));
}
