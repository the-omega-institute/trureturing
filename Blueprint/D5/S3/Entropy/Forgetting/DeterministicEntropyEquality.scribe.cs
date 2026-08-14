using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class DeterministicEntropyEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic finite pushforwards preserve entropy exactly on support-injective maps and lose entropy strictly otherwise.",
        H("Equality and Strict Loss under Deterministic Forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pushforward-entropy-equality-is-support-injectivity"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_eq_iff_injective_on_support"),
                H("Pushforward entropy equality is injectivity on support"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("f"), Underscore, Grp(Star), F.Id("p"), Close,
                    Eq, Sp, F.Id("H"), Open, F.Id("p"), Close, Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("InjOn")), Open, F.Id("f"), Comma, Sp,
                    Operatorname, Grp(F.Id("supp")), Open, F.Id("p"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative mass function on a finite carrier X, " +
                        "and let f : X -> Y be any deterministic map. The entropy of the " +
                        "pushforward equals the entropy of p exactly when f is injective among " +
                        "the atoms x for which p(x) is nonzero.")),
                    Paragraph(Text(
                        "The support qualification is essential. Several zero-mass atoms may lie " +
                        "in one fiber without changing either pushforward mass or entropy. The " +
                        "criterion therefore imposes no injectivity requirement on those atoms " +
                        "and does not replace support by the full carrier.")),
                    Paragraph(Text(
                        "The proof uses the graph-supported joint law of (f(x), x). Its first " +
                        "marginal is the deterministic pushforward and its joint entropy is H(p), " +
                        "so the chain rule turns equality into vanishing conditional entropy. " +
                        "The frozen conditional equality theorem then says that every nonzero-" +
                        "marginal fiber has a point-mass conditional law, which is equivalent to " +
                        "support injectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pushforward-entropy-strict-loss-is-support-collision"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/DeterministicEntropyEquality.pushforward_entropy_lt_iff_not_injective_on_support"),
                H("Strict pushforward entropy loss is a support collision"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("f"), Underscore, Grp(Star), F.Id("p"), Close,
                    Lt, Sp, F.Id("H"), Open, F.Id("p"), Close, Sp, Leftrightarrow, Sp,
                    Neg, Sp, Operatorname, Grp(F.Id("InjOn")), Open, F.Id("f"), Comma, Sp,
                    Operatorname, Grp(F.Id("supp")), Open, F.Id("p"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The entropy loss is strict exactly when two distinct nonzero-mass atoms " +
                        "are identified by f. This is the complementary case of the equality " +
                        "classification, not a separate sufficient-condition witness.")),
                    Paragraph(Text(
                        "For an arbitrary codomain, the nonincrease step factors f through its " +
                        "finite range. The range map is surjective, so the frozen deterministic " +
                        "forgetting theorem applies there; injective relabeling into Y only pads " +
                        "the output law with zero masses and preserves its entropy. Combining " +
                        "that inequality with failure of the equality criterion yields strict " +
                        "decrease."))),
                DescribeRole.Theorem))));
}
