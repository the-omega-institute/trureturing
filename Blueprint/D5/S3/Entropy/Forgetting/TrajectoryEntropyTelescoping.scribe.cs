using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class TrajectoryEntropyTelescopingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stepwise reverse conditional entropy exactly accounts for entropy lost along a deterministic finite trajectory.",
        H("Entropy Telescoping along Deterministic Trajectories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-trajectory-entropy-telescoping"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/TrajectoryEntropyTelescoping."
                        + "deterministic_trajectory_entropy_telescoping"),
                H("Deterministic trajectory entropy telescopes"),
                StatementSource.FromAuthor(TelescopingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be finite, let update : Y -> Y be deterministic, and let the "
                            + "initial mass function be nonnegative and normalized. Define p_k "
                            + "by repeatedly pushing p_0 forward through update. For every positive "
                            + "k, the entropy lost from p_(k-1) to p_k is the conditional entropy "
                            + "of the previous state given the current state.")),
                    Paragraph(Text(
                        "The transition joint law is constructed on the graph of update, with the "
                            + "current state first and the previous state second. Its first marginal "
                            + "is p_k and its joint entropy is H(p_(k-1)). Applying the repository's "
                            + "finite entropy chain rule directly gives the one-step equality.")),
                    Paragraph(Text(
                        "Summing the one-step equality over k = 1 through N cancels all intermediate "
                            + "entropies and proves the finite telescoping identity, including N = 0. "
                            + "The construction encodes the source's deterministic trajectory rather "
                            + "than assuming the entropy identity or defining a loss from its target.")),
                    Paragraph(Text(
                        "Pinned-library searches for finite Shannon conditional entropy, finite entropy "
                            + "chain rules, and deterministic pushforwards found no matching theorem. "
                            + "The repository search found the exact entropy_chain_rule dependency and "
                            + "the pushforward construction, which are imported and applied."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Entropy(Formula law) =>
        Seq(F.Id("H"), Open, law, Close);

    private static Formula Conditional(Formula previous, Formula current) =>
        Seq(F.Id("H"), Open, previous, Sp, Mid, Sp, current, Close);

    private static Formula TelescopingFormula()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("N");
        Formula p = F.Id("p");
        Formula previous = Sub(p, Seq(k, Minus, D(1)));
        Formula current = Sub(p, k);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, k, Sp, Geq, Sp, D(1), Comma, Sp,
            Entropy(previous), Sp, Minus, Sp, Entropy(current), Sp, Eq, Sp,
            Conditional(previous, current), Comma, RowBreak,
            Forall, Sp, n, Comma, Sp,
            Entropy(Sub(p, D(0))), Sp, Minus, Sp, Entropy(Sub(p, n)), Sp, Eq, Sp,
            Sum, Underscore, Grp(Seq(k, Eq, D(1))), Caret, Grp(n), Sp,
            Conditional(previous, current), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
