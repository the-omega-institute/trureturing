using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class GaussInfiniteFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every interior value of the real Gauss map has infinitely many inverse branches.",
        H("Gauss Infinite Fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gauss-map-interior-fiber-infinite"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/GaussInfiniteFiber."
                    + "gauss_map_interior_fiber_infinite"),
                H("Every interior Gauss fiber is infinite"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("y"), InMacro, Sp,
                    Open, D(0), Comma, D(1), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("Infinite")), Open,
                    OpenBrace, F.Id("x"), InMacro, Sp,
                    Open, D(0), Comma, D(1), Close, Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("fract")), Open,
                    Frac, Grp(D(1)), Grp(F.Id("x")), Close,
                    Eq, F.Id("y"), CloseBrace, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix y strictly between zero and one. For each natural n, the point "
                            + "x_n=1/(n+1+y) lies in the open unit interval. Taking the reciprocal "
                            + "and then the fractional part returns y.")),
                    Paragraph(Text(
                        "The branch points are pairwise distinct because inversion and the natural-"
                            + "to-real embedding are injective. Mathlib's infinite-range theorem "
                            + "therefore makes their containing Gauss fiber infinite.")),
                    Paragraph(Text(
                        "This closes only the infinitely-many-inverse-branches clause of residual "
                            + "appendix/E.124. It does not assert invertibility of the natural "
                            + "extension, an invariant measure, or any restart dynamics."))),
                DescribeRole.Theorem))));
}
