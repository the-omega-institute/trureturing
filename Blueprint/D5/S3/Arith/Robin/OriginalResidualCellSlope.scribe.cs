using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalResidualCellSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite cell slope retains shared Mobius cancellation and both real endpoint phases.",
        H("Actual Mobius Cell Slope"),
        Blocks(
            Paragraph(Text(
                "Audit disclosure: the full-telescope registration compiles but remains "
                + "declared_unresolved at IE-C050/source.selection_missing. The missing "
                + "source-coordinate/readout selection and binding evidence are tracked at "
                + "https://github.com/the-omega-institute/trureturing/issues/17898. "
                + "This audit state is separate from the finite mathematical theorem.")),
            Paragraph(Text(
                "For N>=3 and 0<=q<=N-2 put h=q+1, u=log(N/h), "
                + "f(x)=log(N/x)/x, M(j)=sum_{1<=d<=j}mu(d), and "
                + "U_j=sum_{1<=d<=j}mu(d)f(d). All U_j use the same N. "
                + "The integer Mobius function includes every prime power. "
                + "On the real cell N<a<b<2N let k be the Robin density, "
                + "w=integral_a^b k, C=integral_a^b fract(t)k(t), and "
                + "d=U_N(C-w/2)+(w/2)(U_N-U_q)+(w/2)(M(q)+2)f(h).")),
            Describe.Lean(
                DescribeId.Create("actual-cell-slope-payment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalResidualCellSlope.cell_slope_payment"),
                H("Finite cancellation, quantitative payment and signed phase interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact Abel tail is T=sum_{h<=j<N}(M(j)+2)(f(j)-f(j+1)) "
                        + "=U_N-U_q+(M(q)+2)f(h). The literal +2 and the shared "
                        + "prefix cancel before absolute values. With "
                        + "W=sum_{h<=j<N}j(f(j)-f(j+1)), telescoping gives "
                        + "W=u+sum_{h<j<N}f(j), and u<=W<=u+u^2/2. "
                        + "The last inequality uses the antitone sum/integral comparison "
                        + "and the affine-logarithmic integral.")),
                    Paragraph(Text(
                        "Define rho=max_{h<=j<N}|M(j)+2|/j. This is an actual "
                        + "nonempty finite maximum with its bounding property proved. "
                        + "Then |d|<=|U_N|k(a)/8+(w/2)rho(u+u^2/2). "
                        + "No tail estimate is assumed. Both q=0 and q=N-2 are included.")),
                    Paragraph(Text(
                        "Let alpha=min_{h<=j<N}(M(j)+2)/j and "
                        + "beta=max_{h<=j<N}(M(j)+2)/j. Set "
                        + "P(t)=(fract(t)-1/2)^2/2-1/16, "
                        + "B=U_N[k(b)P(b)-k(a)P(a)], and "
                        + "J=|U_N|(k(a)-k(b))/16. The two-sided interval is "
                        + "B+(w/2)alpha W-J<=d<=B+(w/2)beta W+J. "
                        + "It retains W, including when either extremum is negative, "
                        + "and the actual phases at arbitrary real endpoints.")),
                    Paragraph(Text(
                        "The Abel identity is reused from ActualOddMobiusFinitePairing; "
                        + "the integral from QuotientIntegralBudget; the monotone sum "
                        + "comparison from Mathlib; and the translated original Bernoulli "
                        + "primitive from OriginalEarlyDivisorQuadrature. These finite "
                        + "bounds assert no uniform tail sign, signed global account, "
                        + "strict Robin inequality or Riemann hypothesis.")))))));
}
