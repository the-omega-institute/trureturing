using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilBurnolCauchyTailBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilBurnolCauchyTailBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative bounds for actual multi-orbit Weil tests, with explicit finite geometry and scalar spectral-tail premises.",
        H("WeilBurnolCauchyTailBudget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-synthesized-product-le-squared-decay"),
                DeclarationHandle.Create(Prefix + "synthesized_product_le_squared_decay"),
                H("Cauchy-Schwarz for both actual channels"),
                StatementSource.FromAuthor(Disp(F.Id("If |v_i|,|w_i|<=D_i*u with D_i,u>=0, then |sum a_i v_i|*|sum a_i w_i|<=E(a)*(sum D_i^2)*u^2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bound each squared norm by finite Cauchy-Schwarz, then use the nonnegative square of the difference of the norms. Every coefficient cross term is covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-burnolRemainder-eq-exceptional-tail"),
                DeclarationHandle.Create(Prefix + "burnolRemainder_eq_exceptional_tail"),
                H("Exact exceptional-head cancellation"),
                StatementSource.FromAuthor(Disp(F.Id("R_N(a)=Re(sum over n outside P.exceptional of the actual powered convolution-square zero summand)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual killer interpolation makes all non-target exceptional summands zero. Split the absolutely convergent full sum and cancel the exact selected-orbit contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-burnol-uniform-cauchy-tail-bound"),
                DeclarationHandle.Create(Prefix + "burnol_uniform_cauchy_tail_bound"),
                H("Direct quadratic tail coefficient"),
                StatementSource.FromAuthor(Disp(F.Id("For actual two-sided killer decay constants D_i and an actual scalar fourth-moment tail bound Theta, |R_N(a)|<=4^(-(N+1))*(sum D_i^2)*Theta*E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the exact head cancellation, common peak tail, Cauchy-Schwarz and summable comparison. This coefficient bounds the quadratic remainder directly. It is not identified with the old entrywise mixed-majorant total. The BPT positive-ordinate half-endpoint convention requires separate reconciliation with this two-sided full-multiplicity tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-burnol-cauchy-tail-bound-of-two-jets"),
                DeclarationHandle.Create(Prefix + "burnol_cauchy_tail_bound_of_two_jets"),
                H("Discharge transform-decay premises"),
                StatementSource.FromAuthor(Disp(F.Id("Actual unit support and two jet bounds J0_i,J2_i imply the direct tail coefficient (sum (3*(J0_i+J2_i))^2)*Theta."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse zero_transform_pair_le_three_jets for both conjugate evaluations. The jet bounds are finite analytic data, while the scalar spectral tail remains the independent number-theoretic premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-cauchy-budget-full-gram-margin"),
                DeclarationHandle.Create(Prefix + "cauchy_budget_full_gram_margin"),
                H("Apply the existing exact depth selector"),
                StatementSource.FromAuthor(Disp(F.Id("If the explicit direct tail coefficient is <=c/den, then at every N>=rationalQuarterDepth(c,den,p,q), Re(a*G_N a)<=-(4-p/q)E(a), with den,p,q>0."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing integer selector bounds the geometric error. Positive analytic multiplicities give target margin four. The bound is for the actual full Gram, with all infinite-tail cross terms retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-rationalCauchyTailBudget"),
                DeclarationHandle.Create(Prefix + "rationalCauchyTailBudget"),
                H("Executable rational direct coefficient"),
                StatementSource.FromAuthor(Disp(F.Id("C_eff=(sum (3*(J0_i+J2_i))^2)*Theta."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is no finite-head term because the actual head was proved to cancel. The definition evaluates rational arithmetic only; it does not certify zeta zeros or a published analytic estimate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weilburnolcauchytailbudget-rationalCauchyTailBudget-cast"),
                DeclarationHandle.Create(Prefix + "rationalCauchyTailBudget_cast"),
                H("Exact real semantics"),
                StatementSource.FromAuthor(Disp(F.Id("The rational coefficient cast to the reals equals the real coefficient used by the full-Gram margin theorem."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite sums, products and powers commute with the rational-to-real cast."))),
                DescribeRole.Theorem)), []));
}
