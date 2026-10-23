using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalMovingCutBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalMovingCutBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual moving-cut contribution retains its complete signed rows and original measurable selections.",
        H("The Original Moving-Cut Discrepancy"),
        Blocks(
            Paragraph(Text("A direct scalar consequence of the aggregate bound is uniform smallness relative to the original positive mass: 6 ell^(-99/500)log(2ell) tends to zero as ell tends to infinity. For each epsilon>0 choose one ell_0 before R and S; every ell>=ell_0, R>ell and complete measurable S subset [ell,R] with M=volume(S)>0 then satisfy |C_cut(S)+P_cut(S)|<=epsilon M. This is an ordinary limit consequence of the exact compiled bound; no separate Lean limit theorem is claimed. It pays the cut remainder only, and gives no bound on either summand alone, the other paired/early baseline, or the total ordinary-prime signed contribution.")),
            Paragraph(Text("These original proofs reuse OriginalMovingWindowMoment and the native ratio/variation suppliers in OriginalMovingCutRow. Source-owner four-slot audit is unfinished: exact actual/rejected law, bridge and whole-family variation/sensitivity compile, but qualifying actual observational-dependence witnesses and lawful sourceSelection/current binding remain missing. No validated registration is claimed; the concrete gap is tracked at https://github.com/the-omega-institute/trureturing/issues/15968.")),
            Describe.Lean(
                DescribeId.Create("original-cut-row-lattice-estimate"),
                DeclarationHandle.Create(Prefix + "original_cut_row_lattice_estimate"),
                H("A moving-cut row with its continuum compensation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let 256<=ell<R, J=[ell,R], t in J and d>=1 be an integer. "
                        + "Use the same literal kernel, K_J(x)=integral_J k(s,x) ds, "
                        + "N_d(x)=integral_(J intersect {s<d^(500/151)}) k(s,x) ds "
                        + "and r_d(x)=N_d(x)/K_J(x), with zero ratio at zero mass. "
                        + "Write F_(t,d)(x)=log(x/d)k(t,x) "
                        + "(1_{t<d^(500/151)}-r_d(x)) and "
                        + "b(t)=(lambda(t)-lambda(B(t)))/(w(t)t^(11/10)).")),
                    Paragraph(Text(
                        "The complete row remainder is the sum over "
                        + "1<=m<=floor(2R)/d of log(m)k(t,dm) "
                        + "(1_{t<d^(500/151)}-r_d(dm)), minus "
                        + "(1/d)integral_t^B(t) F_(t,d)(x) dx. Its absolute value "
                        + "is at most 3 b(t) log(2t). The height satisfies "
                        + "0<=b(t)<=t^(-3/10). The sum includes the zero log at "
                        + "m=1, every nonzero Mobius row remains available for "
                        + "subsequent signed summation, and the floor is applied "
                        + "before the natural-number division.")),
                    Paragraph(Text(
                        "Cross multiplication of the literal kernels and two "
                        + "integral comparisons show that r_d decreases wherever "
                        + "K_J is positive. Positivity of k(t,x) for t in J "
                        + "implies positivity of K_J(x), including the ends of J. "
                        + "The ratio's zero extension need not decrease. On a "
                        + "single window use the decreasing extension taking "
                        + "value 1 on x<=t and 0 on x>=B(t); multiplication by "
                        + "k(t,x) agrees exactly with the original ratio at "
                        + "all x, including both zero endpoints.")),
                    Paragraph(Text(
                        "For d<=B(t)^(151/500), the logarithmic price body "
                        + "decreases on [t,B(t)]. Its zero extension has the "
                        + "lower-end jump and variation at most 2 b(t)log(2t). "
                        + "The decreasing ratio adds at most b(t)log(2t). "
                        + "For d>=B(t)^(151/500) the original row is zero, "
                        + "since all its positive reference mass precedes "
                        + "the divisor clock. Variation on adjacent lattice "
                        + "cells adds to variation on the full grid. The "
                        + "initial zero cell and the entire last cell are "
                        + "included; the last grid endpoint exceeds 2R.")),
                    Paragraph(Text(
                        "This row estimate supplies no count of crossing "
                        + "integer rows and no summed bound with exponent "
                        + "-99/500. Integral interchange over an arbitrary "
                        + "complete selected S, the favorable paired term, "
                        + "the early-error estimate and cofinal positive-mass "
                        + "original witnesses are not conclusions of this "
                        + "theorem. The full signed Robin/RH obligation "
                        + "remains open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-cut-row-pointwise-budget"),
                DeclarationHandle.Create(Prefix + "original_cut_row_pointwise_budget"),
                H("The complete pointwise crossing budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 256<=ell<R and t in [ell,R], sum the actual "
                        + "signed-row magnitudes over every integer "
                        + "1<=d<=floor(B(t)^(151/500)). Rows with "
                        + "d<=floor((t-t^(4/5))^(151/500)) vanish from the "
                        + "literal strict-left cutoff, including zero-normalizer "
                        + "and endpoint cases. The remaining interval has at most "
                        + "2*t^(51/500) integer labels.")),
                    Paragraph(Text(
                        "Applying the source-specific row estimate and "
                        + "|mu(d)|<=1, then b(t)<=t^(-3/10), gives the complete "
                        + "bound sum_d |mu(d)|*|latticeRowRemainder(ell,R,t,d)| "
                        + "<= 6*t^(-99/500)*log(2t). The original divisor rows "
                        + "remain available with their signed Mobius factors for "
                        + "later aggregation; absolute values pay only this "
                        + "pointwise budget.")),
                    Paragraph(Text(
                        "The complete crossing budget supplies the aggregate "
                        + "estimate below on any measurable complete S. The "
                        + "paired baseline inequality, early-error decay, "
                        + "cofinal witnesses and full signed Robin/RH "
                        + "conclusion remain separate obligations."))),
                DescribeRole.Theorem))));
}
