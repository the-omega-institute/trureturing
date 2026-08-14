using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Mixing;

internal sealed class MixtureEntropyUpperEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The upper finite mixture-entropy bound is sharp exactly when the positive-weight components have pairwise disjoint supports.",
        H("Equality in the Upper Mixture-Entropy Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-mixture-entropy-equality-means-disjoint-active-supports"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Mixing/MixtureEntropyUpperEquality.mixture_entropy_eq_weighted_add_weight_entropy_iff_pairwise_disjoint_supports"),
                H("Upper mixture-entropy equality means disjoint active supports"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("m"), Close, Eq, Sp,
                    F.Id("H"), Open, F.Id("w"), Close, Plus, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("w"), Open, F.Id("i"), Close, Sp,
                    F.Id("H"), Open, F.Id("q"), Underscore, Grp(F.Id("i")), Close,
                    Sp, Leftrightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("PairwiseDisjoint")), Open,
                    Operatorname, Grp(F.Id("supp")), Open, F.Id("w"), Close,
                    Comma, Sp, Open, F.Id("i"), Mapsto, Sp,
                    Operatorname, Grp(F.Id("supp")), Open,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let w be a normalized nonnegative law on a finite selector carrier, " +
                        "and let every q_i be a normalized nonnegative law on a finite output " +
                        "carrier. The entropy of their mixture reaches weighted component " +
                        "entropy plus H(w) exactly when the supports of the components whose " +
                        "weights are nonzero are pairwise disjoint.")),
                    Paragraph(Text(
                        "The support restriction on w is essential. A zero-weight component " +
                        "contributes no joint mass and no weighted entropy, so its support may " +
                        "overlap any other component without affecting equality. Positive-weight " +
                        "components, by contrast, must never assign nonzero mass to the same " +
                        "output.")),
                    Paragraph(Text(
                        "For the selector-output joint law, the chain rule identifies the upper " +
                        "entropy gap with the conditional entropy of the selector given the " +
                        "output. The frozen zero-conditional-entropy characterization makes every " +
                        "positive-output slice a selector point mass. Such point masses are " +
                        "equivalent to each output belonging to at most one positive-weight " +
                        "component support, which is precisely the displayed pairwise " +
                        "disjointness condition."))),
                DescribeRole.Theorem))));
}
