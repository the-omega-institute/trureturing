using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class MetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite total variation satisfies the metric laws, the probability unit bound, and an attained event-gap characterization.",
        H("Metric Laws and Variational Characterization for Finite Total Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("total-variation-is-unconditionally-nonnegative"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_nonneg"),
                H("Total variation is unconditionally nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    D(0), Le, Sp,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Before this module, the TotalVariation bucket contained only the Pinsker " +
                                        "module. Pinsker bounded total variation by relative entropy, measured in " +
                                        "nats, but did not establish a single basic metric property of total " +
                                        "variation, not even nonnegativity.")),
                                    Paragraph(Text(
                                        "The present declaration supplies that first property for arbitrary finite " +
                                        "real mass functions. No sign or normalization hypothesis is present: each " +
                                        "coordinate contributes an absolute value, the finite sum is nonnegative, " +
                                        "and multiplication by one half preserves the order."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("total-variation-separates-finite-real-mass-functions"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_eq_zero_iff"),
                H("Total variation separates finite real mass functions"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Eq, D(0), Sp, Leftrightarrow, Sp, F.Id("p"), Eq, F.Id("q"), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Vanishing is equivalent to equality of the two functions. If the half-L1 " +
                                        "sum vanishes, the finite sum of nonnegative absolute differences is zero; " +
                                        "hence every coordinate difference is zero. Conversely, substituting equal " +
                                        "functions makes every summand vanish.")),
                                    Paragraph(Text(
                                        "This separation result is again unconditional. It depends on the zero set " +
                                        "of the absolute value and on a finite sum of nonnegative terms, not on an " +
                                        "interpretation of p and q as probability vectors."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("total-variation-is-symmetric"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_comm"),
                H("Total variation is symmetric"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Eq,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("q"), Comma, Sp, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Symmetry follows coordinatewise from the symmetry of absolute " +
                                        "subtraction. Exchanging p and q changes each signed difference to its " +
                                        "negative and leaves its absolute value, the finite sum, and the factor one " +
                                        "half unchanged.")),
                                    Paragraph(Text(
                                        "Accordingly, symmetry requires neither nonnegative coordinates nor equal " +
                                        "total mass. It is a property of the absolute-value expression itself."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("total-variation-satisfies-the-triangle-inequality"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_triangle"),
                H("Total variation satisfies the triangle inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Comma, Sp, F.Id("r"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("r"), Close,
                                    Le, Sp,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Plus,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("q"), Comma, Sp, F.Id("r"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The scalar triangle inequality is applied to p(i)-r(i), decomposed as " +
                                        "p(i)-q(i) plus q(i)-r(i), and is then summed over the finite index type. " +
                                        "Distributivity of finite sums and the nonnegative factor one half give the " +
                                        "displayed inequality.")),
                                    Paragraph(Text(
                                        "Nonnegativity, separation, symmetry, and the triangle inequality therefore " +
                                        "hold with no assumptions beyond finiteness. Structurally, all four are " +
                                        "properties of absolute value and finite sums rather than properties of " +
                                        "probability. Together they make total variation a genuine metric on finite " +
                                        "real mass functions, although this module proves the laws directly and does " +
                                        "not register a MetricSpace instance."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("probability-vectors-have-total-variation-at-most-one"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_le_one"),
                H("Probability vectors have total variation at most one"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Land, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Le, Sp, D(1), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The unit bound is the first result in this module that uses probability " +
                                        "hypotheses. Coordinatewise nonnegativity gives |p(i)-q(i)| <= p(i)+q(i); " +
                                        "normalization makes the sum on the right equal to two, and the defining " +
                                        "factor one half yields the bound one.")),
                                    Paragraph(Text(
                                        "Both parts of each probability-vector hypothesis are necessary to this " +
                                        "argument as formalized: p and q are nonnegative and each has total mass " +
                                        "one. These assumptions are absent from the four metric laws and are " +
                                        "stronger than the equal-mass premise used by the variational theorem below."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("total-variation-is-the-greatest-attained-event-gap"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Metric.total_variation_eq_sup_event_gap"),
                H("Total variation is the greatest attained event gap"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("p"), Open, F.Id("i"), Close, Eq,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("q"), Open, F.Id("i"), Close,
                                    Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("IsGreatest")), Open,
                                    Operatorname, Grp(F.Id("range")), Open,
                                    F.Id("A"), Colon, Sp,
                                    Operatorname, Grp(F.Id("Finset")), Open, Iota, Close,
                                    Mapsto, Sp,
                                    Vert, Sp,
                                    Open,
                                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("A")),
                                    F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Minus,
                                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("A")),
                                    F.Id("q"), Open, F.Id("i"), Close,
                                    Sp, Vert, Close, Comma, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "This is the result with the principal interpretive content: total " +
                                        "variation is the largest probability-mass gap achievable over events. " +
                                        "The statement applies more generally to arbitrary finite real mass " +
                                        "functions whose total masses are equal. It requires neither coordinatewise " +
                                        "nonnegativity nor normalization to one.")),
                                    Paragraph(Text(
                                        "The theorem deliberately uses IsGreatest rather than a literal supremum. " +
                                        "Membership in the stated range records, in the theorem's own type, that a " +
                                        "concrete event attains total variation; the upper-bound field records that " +
                                        "no event has a larger gap. A literal iSup formulation would introduce " +
                                        "conditionally-complete-lattice machinery and obscure attainment. A " +
                                        "Finset.sup' fold over the powerset would require a separate nonemptiness " +
                                        "witness and hide the maximum behind fold infrastructure.")),
                                    Paragraph(Text(
                                        "The attaining event is the dominance set {i | q(i) <= p(i)}. On this event " +
                                        "the signed excess is nonnegative and equals total variation by the frozen " +
                                        "pinning identity total_variation_eq_sum_positive from the Pinsker module. " +
                                        "For an arbitrary event, discarding its negative contributions bounds its " +
                                        "signed gap by the same dominance-set excess; applying the argument in the " +
                                        "reverse order controls the opposite sign and hence the absolute gap.")),
                                    Paragraph(Text(
                                        "The upper-bound field is not vacuous. For two disjoint unit point masses on " +
                                        "Bool, total variation is one, whereas the empty event has gap zero and, more " +
                                        "tellingly, the whole index set also has gap zero because the total masses " +
                                        "are equal. Thus the maximum is emphatically not attained by every event. " +
                                        "More generally, for any unequal equal-mass pair, the whole event has zero " +
                                        "gap and cannot attain the positive maximum. This Bool witness was compiled " +
                                        "independently of the formal proof.")),
                                    Paragraph(Text(
                                        "With these declarations in place, later total-variation developments can " +
                                        "invoke the basic metric properties rather than re-derive them, and Pinsker's " +
                                        "divergence bound in nats now sits inside a metric structure rather than " +
                                        "standing alone. No reverse bound of Bretagnolle-Huber type, " +
                                        "measure-theoretic analogue, completeness theorem, or topological statement " +
                                        "about the induced metric is claimed. Nor is a MetricSpace instance " +
                                        "registered: the metric properties are proved, not packaged."))),
                DescribeRole.Theorem
            ))));
}
