using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class HellingerDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared Hellinger distance is dominated by KL divergence and satisfies its finite square-root metric laws.",
        H("Squared Hellinger Distance, Divergence, and Metric Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("squared-hellinger-distance-is-dominated-by-kl-divergence"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_le_kl_divergence"),
                H("Squared Hellinger distance is dominated by KL divergence"),
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
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Land, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Land, RowBreak,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0),
                                    Sp, Rightarrow, Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                                    Sp, Rightarrow, RowBreak,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Le, Sp,
                                    F.Id("D"), Open,
                                    F.Id("p"), Sp, Bar, Bar, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For nonnegative normalized finite mass functions p and q satisfying " +
                                        "discrete absolute continuity p << q, squared Hellinger distance is at " +
                                        "most the KL divergence D(p||q). Divergence is measured in nats.")),
                                    Paragraph(Text(
                                        "The proof is an assembly of frozen results rather than a fresh analytic " +
                                        "argument. The frozen estimate exp(-D) <= BC^2, together with positivity " +
                                        "of the exponential and nonnegativity of the Bhattacharyya coefficient, " +
                                        "gives exp(-D/2) <= BC. The frozen bridge H^2=2(1-BC) then yields " +
                                        "H^2 <= 2(1-exp(-D/2)). Finally, mathlib's Real.add_one_le_exp gives " +
                                        "1-exp(-x) <= x at x=D/2 and closes the chain.")),
                                    Paragraph(Text(
                                        "Nonnegativity of D is supplied by the frozen kl_divergence_nonneg " +
                                        "theorem; it is not an additional assumption. Real.add_one_le_exp holds " +
                                        "for every real argument, so the scalar library fact is stronger than " +
                                        "the nonnegative-domain estimate needed by this proof.")),
                                    Paragraph(Text(
                                        "Warning: H^2 <= D and the frozen inequality H^2/2 <= TV point in the " +
                                        "same direction away from H^2. They cannot be chained to bound total " +
                                        "variation above by the divergence. Pinsker and Bretagnolle--Huber give " +
                                        "that upper control; the present comparison serves a different purpose. " +
                                        "The reversed chain is not supported by this module."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("hellinger-kl-domination-is-strict-on-a-bool-witness"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_lt_kl_divergence_witness"),
                H("Hellinger--KL domination is strict on a Bool witness"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    F.Id("p"), Open, Operatorname, Grp(F.Id("true")), Close,
                                    Eq, D(1), Comma, Sp,
                                    F.Id("p"), Open, Operatorname, Grp(F.Id("false")), Close,
                                    Eq, D(0), Comma, RowBreak,
                                    F.Id("q"), Open, Operatorname, Grp(F.Id("true")), Close,
                                    Eq, Frac, Grp(D(1)), Grp(D(4)), Comma, Sp,
                                    F.Id("q"), Open, Operatorname, Grp(F.Id("false")), Close,
                                    Eq, Frac, Grp(D(3)), Grp(D(4)), Comma, RowBreak,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                                    Eq, D(1), Lt,
                                    Log, Sp, D(4), Eq,
                                    F.Id("D"), Open,
                                    F.Id("p"), Sp, Bar, Bar, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Strictness is itself kernel-checked. On Bool, p is the point mass at " +
                                        "true and q assigns masses 1/4 and 3/4 to true and false. Lean computes " +
                                        "H^2(p,q)=1 and D(p||q)=log 4, then verifies 1 < log 4. Thus the main " +
                                        "bound is not an identity disguised as an inequality."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("squared-hellinger-distance-is-unconditionally-nonnegative"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_nonneg"),
                H("Squared Hellinger distance is unconditionally nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    D(0), Le, Sp,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Nonnegativity holds for arbitrary finite real functions. No pointwise " +
                                        "sign condition, normalization, or support hypothesis appears: the result " +
                                        "is the coordinatewise nonnegativity of squares summed over a finite type."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("squared-hellinger-distance-is-unconditionally-symmetric"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_comm"),
                H("Squared Hellinger distance is unconditionally symmetric"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("q"), Comma, Sp, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Symmetry likewise holds on all finite real functions without " +
                                        "hypotheses. Exchanging p and q negates each square-root gap and leaves " +
                                        "its square unchanged."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-zero-set-is-square-root-equality-with-an-exact-domain-boundary"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_eq_zero_iff_sqrt_eq"),
                H("The zero set is square-root equality with an exact domain boundary"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    F.Id("H"), Caret, Grp(D(2)), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq, D(0),
                                    Sp, Leftrightarrow, Sp, RowBreak,
                                    Open, F.Id("i"), Mapsto, Sp,
                                    Sqrt, Sp, Grp(F.Id("p"), Open, F.Id("i"), Close), Close,
                                    Eq,
                                    Open, F.Id("i"), Mapsto, Sp,
                                    Sqrt, Sp, Grp(F.Id("q"), Open, F.Id("i"), Close), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The vanishing characterization consists of three inseparable statements. " +
                                        "One might expect the conclusion to mirror total_variation_eq_zero_iff, " +
                                        "which separates arbitrary finite real functions with no hypotheses. It " +
                                        "does not, and the precise unconditional theorem is instead " +
                                        "hellinger_sq_eq_zero_iff_sqrt_eq: H^2 vanishes exactly when the " +
                                        "coordinatewise square-root functions agree.")),
                                    Paragraph(Text(
                                        "The obstruction is not relegated to a caveat. The theorem " +
                                        "hellinger_sq_negative_counterexample takes Unit with the constant " +
                                        "functions p=-1 and q=-2. They are distinct, but Real.sqrt annihilates " +
                                        "both, so H^2(p,q)=0. The counterexample is a theorem in the module, not " +
                                        "a remark: the limitation is kernel-checked and frozen alongside the " +
                                        "characterization.")),
                                    Paragraph(Text(
                                        "The companion theorem hellinger_sq_eq_zero_iff recovers separation " +
                                        "exactly on the pointwise nonnegative cone: if p(i) and q(i) are " +
                                        "nonnegative for every coordinate, then H^2(p,q)=0 if and only if p=q. " +
                                        "No normalization is required for this recovery.")),
                                    Paragraph(Text(
                                        "The comparison with total variation is therefore exact. Total variation " +
                                        "separates points everywhere, whereas squared Hellinger distance separates " +
                                        "points only where the square root is injective. Real.sqrt collapses the " +
                                        "entire nonpositive half-line, and pointwise nonnegativity is precisely the " +
                                        "domain restriction that removes this obstruction."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-square-root-hellinger-distance-satisfies-the-triangle-inequality"),
                DeclarationHandle.Create("D5/S3/TotalVariation/HellingerDivergence.sqrt_hellinger_sq_triangle"),
                H("The square-root Hellinger distance satisfies the triangle inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Comma, Sp,
                                    F.Id("r"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Sqrt, Sp, Grp(
                                        F.Id("H"), Caret, Grp(D(2)), Open,
                                        F.Id("p"), Comma, Sp, F.Id("r"), Close),
                                    Le, Sp,
                                    Sqrt, Sp, Grp(
                                        F.Id("H"), Caret, Grp(D(2)), Open,
                                        F.Id("p"), Comma, Sp, F.Id("q"), Close),
                                    Plus,
                                    Sqrt, Sp, Grp(
                                        F.Id("H"), Caret, Grp(D(2)), Open,
                                        F.Id("q"), Comma, Sp, F.Id("r"), Close), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The theorem is stated for sqrt(H^2), the Hellinger distance itself, and " +
                                        "holds for arbitrary finite real functions with no hypotheses. Together " +
                                        "with unconditional nonnegativity and symmetry, it records the metric " +
                                        "laws that survive on the all-real domain; point separation remains " +
                                        "restricted exactly as described above.")),
                                    Paragraph(Text(
                                        "The triangle inequality cost nothing to obtain. It is Minkowski's " +
                                        "inequality in l2, obtained by applying mathlib's existing Real.Lp_add_le " +
                                        "at exponent two to the two coordinatewise square-root gaps. Their sum " +
                                        "is the direct p-to-r gap.")),
                                    Paragraph(Text(
                                        "No new definition, normed-space instance, or EuclideanSpace " +
                                        "wrapper was introduced. Building such scaffolding to reach a single " +
                                        "inequality would not have been worthwhile, and the existing finite Lp " +
                                        "theorem made it unnecessary.")),
                                    Paragraph(Text(
                                        "The TotalVariation bucket now contains Pinsker's bound, the metric " +
                                        "structure with the attained variational characterization, data-processing " +
                                        "contraction, Bretagnolle--Huber with the Bhattacharyya coefficient, the " +
                                        "Hellinger comparison with total variation, and now the Hellinger--KL " +
                                        "comparison together with these square-root metric properties. All " +
                                        "divergence units in this narrative are nats.")),
                                    Paragraph(Text(
                                        "No Renyi divergence, reverse bound of D by H^2, equality analysis, or " +
                                        "measure-theoretic analogue is claimed."))),
                DescribeRole.Theorem
            ))));
}
