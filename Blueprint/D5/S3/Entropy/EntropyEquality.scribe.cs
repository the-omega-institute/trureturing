using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class EntropyEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two endpoints of the finite Shannon-entropy bracket in nats characterize the uniform law and point masses.",
        H("Equality Cases for Finite Shannon Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximum-entropy-characterizes-the-uniform-law"),
                DeclarationHandle.Create("D5/S3/Entropy/EntropyEquality.entropy_eq_log_card_iff_uniform"),
                H("Maximum entropy characterizes the uniform law"),
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
                                    F.Id("H"), Open, F.Id("p"), Close, Eq,
                                    Log, Open,
                                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                                    Close, Sp, Leftrightarrow, Sp, RowBreak,
                                    F.Id("p"), Eq,
                                    Open, F.Id("i"), Mapsto, Sp,
                                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                                    Caret, Grp(Minus, D(1)), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The entropy bucket already brackets every normalized nonnegative mass " +
                                        "function between 0 and log card. This theorem settles the upper " +
                                        "endpoint: the maximum is attained exactly at the uniform law. Together " +
                                        "with the point-mass characterization below, it identifies both equality " +
                                        "cases of that bracket.")),
                                    Paragraph(Text(
                                        "The upper endpoint is a composition of two deposited results. The " +
                                        "entropy-divergence identity says that divergence from the uniform law " +
                                        "is exactly the entropy deficit log card - H(p), while GibbsEquality's " +
                                        "zero-divergence criterion says that this divergence vanishes exactly " +
                                        "when the two laws agree. The identity was originally proved to pin the " +
                                        "entropy definition against corruption; here it serves as an ingredient " +
                                        "for a different theorem, so a deposited result has become raw material.")),
                                    Paragraph(Text(
                                        "The hypotheses are nonnegativity and normalization only; no strict " +
                                        "positivity is required, and zero-mass letters are permitted. The units " +
                                        "are nats because shannonEntropy uses Real.log. Nonempty is required only " +
                                        "for this upper endpoint, where cardinality zero would make the uniform " +
                                        "law ill-defined; the lower endpoint carries no Nonempty hypothesis.")),
                                    Paragraph(Text(
                                        "No quantitative statement is made about how far entropy falls below the " +
                                        "bound for a near-uniform law: there is no stability theorem or deficit " +
                                        "estimate. Nothing is claimed about the equality cases of conditional " +
                                        "entropy."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("zero-entropy-characterizes-point-masses"),
                DeclarationHandle.Create("D5/S3/Entropy/EntropyEquality.entropy_eq_zero_iff_point_mass"),
                H("Zero entropy characterizes point masses"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
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
                                    F.Id("H"), Open, F.Id("p"), Close, Eq, D(0),
                                    Sp, Leftrightarrow, Sp, RowBreak,
                                    Exists, Sp, F.Id("i"), Comma, Sp,
                                    F.Id("p"), Eq, Open,
                                    F.Id("j"), Mapsto, Sp,
                                    Begin, Grp(F.Id("cases")),
                                    D(1), Comma, Amp, F.Id("j"), Eq, F.Id("i"), RowBreak,
                                    D(0), Comma, Amp, F.Id("j"), Neq, Sp, F.Id("i"),
                                    End, Grp(F.Id("cases")), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "This theorem settles the lower endpoint of the same entropy bracket: " +
                                        "entropy vanishes exactly at a point mass. Here point mass has the exact " +
                                        "form displayed in the statement: one index carries mass 1 and every " +
                                        "other index carries mass 0.")),
                                    Paragraph(Text(
                                        "The lower endpoint is not a rewrite of entropy nonnegativity. Each mass " +
                                        "lies in the unit interval, so every Real.negMulLog summand is " +
                                        "nonnegative. A vanishing finite sum of nonnegative terms forces every " +
                                        "summand to vanish, and the zeros of Real.negMulLog on that interval are " +
                                        "exactly 0 and 1. The unit sum then leaves precisely one index carrying " +
                                        "mass 1 and forces all remaining masses to be 0.")),
                                    Paragraph(Text(
                                        "As above, the only distributional hypotheses are nonnegativity and " +
                                        "normalization; strict positivity is not assumed, and zero-mass letters " +
                                        "are permitted. The units are nats. Unlike the maximum statement, this " +
                                        "signature needs no Nonempty instance: normalization itself rules out an " +
                                        "empty alphabet, while no uniform law has to be formed.")),
                                    Paragraph(Text(
                                        "This equality characterization is qualitative only. It provides no " +
                                        "stability or entropy-deficit estimate for laws near a point mass, and it " +
                                        "does not characterize equality for conditional entropy."))),
                DescribeRole.Theorem
            ))));
}
