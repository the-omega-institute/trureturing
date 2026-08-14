using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Displacement;

internal sealed class GoldenDisplacementSurfaceRegionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-exponent slices determine the exact convergence region of the golden displacement surface, including its hidden-product threshold and a point beyond the former half-plane.",
        H("The Exact Golden Displacement Surface Region"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-substitution-start-has-a-linear-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "goldenSubstStart_linear_lower_bound"),
                H("The substitution start has a linear lower bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Colon, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Varphi, Sp, F.Id("v"), Plus, Varphi, Sp, Minus,
                    D(2), Leq, Sp, Operatorname, Grp(F.Id("goldenSubstStart")),
                    Open, F.Id("v"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen beta identity expresses the substitution start as the golden Euler exponent plus its conjugate linear part. Combining it with the frozen beta growth estimate and the standard golden-ratio identities gives the stated lower bound without new floor analysis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-power-terms-are-single-real-powers"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "dTerm_prime_pow_rpow"),
                H("Prime-power terms are single real powers"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Sp,
                    Rightarrow, Sp, F.Id("dTerm"), Open, F.Id("s"), Comma, Sp,
                    F.Id("w"), Comma, Sp, F.Id("p"), Caret, F.Id("e"), Close,
                    Eq, Sp, F.Id("p"), Caret, Grp(Minus, Open,
                    F.Id("s"), Sp, Operatorname, Grp(F.Id("goldenSubstStart")),
                    Open, F.Id("e"), Close, Plus, F.Id("w"), Sp, F.Id("e"),
                    Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen prime-power monomial factors have the same positive base. Real-power multiplication therefore combines their two exponents into one exact exponent account."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-prime-slice-criterion-is-exact"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "dTerm_summable_iff"),
                H("The prime-slice criterion is exact"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Leq, Sp, F.Id("s"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open, F.Id("dTerm"),
                    Open, F.Id("s"), Comma, Sp, F.Id("w"), Close, Close,
                    Sp, Iff, Sp, Forall, Sp, F.Id("k"), Comma, Sp, D(1), Lt,
                    Sp, F.Id("s"), Sp, Operatorname,
                    Grp(F.Id("goldenSubstStart")), Open,
                    Grp(F.Id("k"), Plus, D(1)), Close, Plus, F.Id("w"), Sp,
                    Grp(F.Id("k"), Plus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Necessity restricts a summable surface to every fixed positive prime-exponent slice, where the exact prime rpow criterion forces exponent greater than one. For sufficiency, the exponent at the second slice makes the asymptotic slope positive. A natural shift then removes the finitely many small slices, and the linear substitution bound supplies a geometric majorant for the remaining product sum. The frozen nonnegative Euler bridge promotes the summable prime-power tail to the global series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-hidden-product-axis-has-threshold-one-half"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "nS_dirichlet_summable_iff"),
                H("The hidden-product axis has threshold one half"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Summable")), Open, F.Id("dTerm"),
                    Open, F.Id("s"), Comma, Sp, D(0), Close, Close, Sp, Iff,
                    Sp, Frac, Grp(D(1)), Grp(D(2)), Lt, Sp, F.Id("s")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first prime slice is the prime series with exponent minus twice s, so summability forces s above one half. Conversely every positive substitution start is at least two, and the exact slice criterion sums the full hidden-product Dirichlet series above that threshold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-former-half-plane-lies-in-the-exact-region"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "exponent_gt_one_of_half_plane"),
                H("The former half-plane lies in the exact region"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Leq, Sp, F.Id("s"), Comma, Sp, D(1), Lt, Sp,
                    F.Id("s"), Plus, F.Id("w"), Sp, Rightarrow, Sp, Forall,
                    Sp, F.Id("k"), Comma, Sp, D(1), Lt, Sp, F.Id("s"), Sp,
                    Operatorname, Grp(F.Id("goldenSubstStart")), Open,
                    Grp(F.Id("k"), Plus, D(1)), Close, Plus, F.Id("w"), Sp,
                    Grp(F.Id("k"), Plus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The substitution start dominates its exponent. Multiplying by nonnegative s shows that every exact prime-slice exponent dominates the former half-plane exponent, recovering the frozen sufficient condition as a corollary of the sharper region."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-convergent-point-lies-outside-the-former-half-plane"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion."
                        + "summable_dTerm_outside_half_plane"),
                H("A convergent point lies outside the former half-plane"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Summable")), Open, F.Id("dTerm"),
                    Open, D(1), Comma, Sp, Minus, Frac, Grp(D(1)), Grp(D(2)),
                    Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At s equal to one and w equal to minus one half, the exact exponent criterion holds: the first slice is computed directly, while all later slices follow from the linear golden lower bound. Yet s plus w is only one half, so this witness lies strictly beyond the formerly known sufficient half-plane."))),
                DescribeRole.Theorem))));
}
