using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MaxEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Shannon entropy in nats is at most the natural logarithm of the alphabet cardinality.",
        H("Maximum Entropy on a Finite Alphabet"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-shannon-entropy-is-at-most-log-cardinality"),
                DeclarationHandle.Create("D5/S3/Entropy/MaxEntropy.entropy_le_log_card"),
                H("Finite Shannon entropy is at most log-cardinality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Nonempty")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Sum, Underscore, Grp(F.Id("i")),
                    Operatorname, Grp(F.Id("negMulLog")), Open,
                    F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Le, Sp,
                    Log, Open,
                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The units are nats: Real.log is the natural logarithm, consistent " +
                        "with the repository's klDivergence. The definition deliberately " +
                        "wraps Mathlib's Real.negMulLog term by term and supplies only the " +
                        "finite sum that Mathlib does not provide. This division of " +
                        "responsibility is deliberate: Mathlib owns the per-term lemmas for " +
                        "nonnegativity on the unit interval, the product rule, and concavity; " +
                        "open-coding -sum p log p and re-deriving them would duplicate " +
                        "upstream work.")),
                    Paragraph(Text(
                        "The proof introduces the uniform distribution u(i) = (card iota)^-1 " +
                        "locally. It is deliberately not frozen as a definition of this " +
                        "module because it has exactly one consumer. The bound is obtained " +
                        "from D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg through " +
                        "the identity D(p||uniform) = log card - H(p); no part of KL " +
                        "nonnegativity is re-proved here.")),
                    Paragraph(Text(
                        "The hypotheses are nonnegativity and normalization only, not strict " +
                        "positivity. Zero-mass letters are permitted. Their terms vanish " +
                        "because Real.negMulLog 0 = 0 and Real.log 0 = 0, following the same " +
                        "endpoint convention already fixed by klDivergence.")),
                    Paragraph(Text(
                        "The Nonempty iota hypothesis is genuinely required, not decorative: " +
                        "without it the cardinality is zero and the uniform mass fails to be " +
                        "a distribution.")),
                    Paragraph(Text(
                        "This module proves the upper bound only. It does not characterize the " +
                        "equality case that the maximum is attained exactly at the uniform " +
                        "distribution. It introduces no conditional or joint entropy."))),
                DescribeRole.Theorem))));
}
