using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordNewtonPositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every record Newton kernel has nonnegative coefficients after actual scalar substitution.",
        H("Unbounded Positivity of the Separable Record Newton Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-q-record-newton-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordNewtonPositivity.actual_q_record_newton_nonnegative"),
                H("Every natural kernel index and every natural length index"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("coeff", F.Id("n"), Call("subst", F.Id("q"),
                        Call("G", F.Id("r")))), Ge, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem quantifies over all natural r and n. The scalar q(t) is "
                        + "the actual positive 2413/3142-avoider counting series, identified "
                        + "by the frozen cardinality supplier with t*largeSchroderSeries. "
                        + "It satisfies q=t+tq+q^2 and t(1+q)=q(1-q). Its constant is zero "
                        + "and every coefficient is nonnegative.")),
                    Paragraph(Text(
                        "In an independent formal variable u, put a=u(3+2u), "
                        + "b=u(1+u)^3 and c=u(4+3u)=4b-a^2. The source constructs "
                        + "M(z)=(1-az)^(-1) C(bz^2/(1-az)^2) from Mathlib's Catalan "
                        + "series C. Its coefficient T_r satisfies T_0=1, T_1=a and "
                        + "(r+4)T_(r+2)=(2r+5)aT_(r+1)+(r+1)cT_r at every index.")),
                    Paragraph(Text(
                        "Define G_r=(1+u)^2(T_r+T_(r+1)) "
                        + "-u(1-u)(1+u)(T_r+2T_(r+1)+T_(r+2)). "
                        + "The conclusion is coefficientwise nonnegativity of G_r(q(t)), "
                        + "without a cutoff in either index. For a polynomial f, the proof "
                        + "constructs V with (1-2u-u^2)V=(1+u)^2 f'. Exact initial "
                        + "coefficient identities and the universal recurrence "
                        + "v_(m+2)=2v_(m+1)+v_m prove V is nonnegative. The chain rule "
                        + "and formal integration prove f(q(t)) is nonnegative when f(0)>=0.")),
                    Paragraph(Text(
                        "This certificate rule treats G_0 through G_11. Let "
                        + "E1=(1+u)^2(1-u-2u^2+3u^3) and "
                        + "E2=(1+u)^2(1-2u-2u^2+4u^3). Two consecutive certificates "
                        + "for E1*T_1 and E1*T_2 propagate to every r>=1. Two for "
                        + "E2*T_13 and E2*T_14 propagate to every r>=13. The universal "
                        + "Motzkin recurrence gives "
                        + "(r+4)G_r=(r+4)(E1*T_r+E2*T_(r+1)) "
                        + "+3u(1-u)(1+u)(cT_r+aT_(r+1)). After substitution the last "
                        + "summand is nonnegative by t(1+q)=q(1-q). This proves "
                        + "every r>=12 and completes the all-index sign law.")),
                    Paragraph(Text(
                        "The new content is the live all-index differential recurrence "
                        + "and positivity propagation, with all necessary steps local to "
                        + "one public theorem. Local definitions and compiler-generated "
                        + "equations receive no separate novelty credit. This is a partial "
                        + "unbounded result. The normalized actual J coefficient formula "
                        + "and its Newton transform are still needed before this sign law "
                        + "implies the actual declining comparisons at every k>=4. "
                        + "Those comparisons, the global maximum at three and complete "
                        + "CKZ Conjecture 2 remain open. No KPI increment is claimed. "
                        + "Reg enrollment is user-paused; no completed escape audit is claimed."))),
                DescribeRole.Theorem))));
}
