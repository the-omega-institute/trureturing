using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class JointAxisLogarithmDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint Robin logarithm is nonzero on an explicit integer cone and has a cubic first-coordinate sensitivity bound.",
        H("Joint logarithm for the Robin clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("omegathree"),
                DeclarationHandle.Create(Gid + ".omegaThree"),
                H("The joint logarithm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def omegaThree (h p q : ℝ) : ℝ := h * log (3 * p / (p + q)) - q * log (2 * p / (p + h))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("omegathree-ne-zero"),
                DeclarationHandle.Create(Gid + ".omegaThree_ne_zero"),
                H("Nonvanishing in the positive integer cone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem omegaThree_ne_zero {p h q : ℕ} (hh : 0 < h) (hp : h < p) (hlo : 11 * h < 7 * q) (hhi : 5 * q < 8 "
                        + "* h) : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0")),
                    Paragraph(Text("The rational cutoff separation bound is positive on the integer cone. "
                        + "Its logarithmic expression is the negative of the joint form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omegathree-hasderivat-p"),
                DeclarationHandle.Create(Gid + ".omegaThree_hasDerivAt_p"),
                H("The first partial derivative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem omegaThree_hasDerivAt_p {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) : HasDerivAt (fun x : "
                        + "ℝ => omegaThree h x q) (-(h * q * (q - h) / (p * (p + h) * (p + q)))) p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omegathree-hasderivat-q"),
                DeclarationHandle.Create(Gid + ".omegaThree_hasDerivAt_q"),
                H("The second partial derivative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem omegaThree_hasDerivAt_q {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) : HasDerivAt (fun y : "
                        + "ℝ => omegaThree h p y) (-log 2 + log (1 + h / p) - h / (p + q)) q"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-omegathree-sub-le"),
                DeclarationHandle.Create(Gid + ".abs_omegaThree_sub_le"),
                H("Sensitivity to the two label errors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem abs_omegaThree_sub_le {h p q s r X : ℝ} (hh : 1 ≤ h) (hX : 4 ≤ X) (hs : X ≤ s) (hr₁ : 3 / 2 ≤ r) "
                        + "(hr₂ : r ≤ 2) (hp : |p - h * s| ≤ 1 / 2) (hq : |q - h * r| ≤ 1 / 2) : |omegaThree h p q - omegaThree h "
                        + "(h * s) (h * r)| ≤ 48 / X ^ 3 * |p - h * s| + 2 * |q - h * r|")),
                    Paragraph(Text("Apply the mean value bound separately in each coordinate along the rectangle joining the two pairs. "
                        + "The first partial derivative scales as the inverse cube of X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omegathree-at-root-phases"),
                DeclarationHandle.Create(Gid + ".omegaThree_at_root_phases"),
                H("Cancellation at the root phases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem omegaThree_at_root_phases {h L a b e₂ e₃ : ℝ} (hh : 0 < h) (hL : 0 < L) (ha : 0 < a) (hb : 0 < "
                        + "b) (haEq : a + log (1 + a / L) = log 2 + e₂) (hbEq : b + log (1 + b / L) = log 3 + e₃) : omegaThree h (h "
                        + "* (L / a)) (h * (b / a)) = h * ((b / a) * e₂ - e₃)")),
                    Paragraph(Text("The two positive logarithm arguments reduce to 3/(1+b/L) and 2/(1+a/L). Substituting the root "
                        + "equations cancels the linear offsets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omegathree-ne-zero-int"),
                DeclarationHandle.Create(Gid + ".omegaThree_ne_zero_int"),
                H("Nonvanishing for signed integer labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem omegaThree_ne_zero_int {p h q : ℤ} (hh : 0 < h) (hp : h < p) (hlo : 11 * h < 7 * q) (hhi : 5 * q "
                        + "< 8 * h) : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0"))),
                DescribeRole.Theorem))));
}
