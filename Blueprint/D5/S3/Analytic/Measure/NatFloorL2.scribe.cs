using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Measure;

internal sealed class NatFloorL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A square-summable real sequence on the positive natural indices defines an L2 natural-floor step function on the Lebesgue half-line (1,infinity).",
        H("Square-summable natural-floor step functions"), Blocks(
            Describe.Lean(DescribeId.Create("nat-floor-l2-summable-squares"),
                DeclarationHandle.Create("D5/S3/Analytic/Measure/NatFloorL2.memLp_nat_floor_of_summable_sq"),
                H("From sequence squares to half-line L2 membership"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Colon, Seq(Mathbb, Grp(F.Id("N"))), To,
                    Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
                    Call("Summable", Seq(Open, F.Id("n"), Mapsto, Sp,
                        Call("a", Seq(F.Id("n"), Plus, D(1))), Caret, Grp(D(2)), Close)),
                    Rightarrow, Sp,
                    Call("MemLp", Seq(Open, F.Id("x"), Mapsto, Sp,
                        Call("a", Call("NatFloor", F.Id("x"))), Close), D(2),
                        Seq(Call("volume"), Mid, Open, D(1), Comma, Infty, Close))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every a : N -> R, assume that the real series of "
                        + "a(n+1)^2 is summable. Then x |-> a(Nat.floor x) belongs to "
                        + "MemLp with exponent 2 for Lebesgue volume restricted to (1,infinity). "
                        + "NatFloor in the formula denotes the natural-valued floor. There is "
                        + "no condition on a(0), no sign condition, and no finite support assumption.")),
                    Paragraph(Text("The countably many cells [n+1,n+2), n in N, cover "
                        + "[1,infinity). On the nth cell the floor is n+1, so the squared "
                        + "step function is constant and its integral is a(n+1)^2. "
                        + "The summable cell integrals give genuine integrability on the union "
                        + "by integrableOn_iUnion_of_summable_integral_norm. Restriction to "
                        + "(1,infinity), measurability of the natural floor, and "
                        + "memLp_two_iff_integrable_sq give the conclusion. This is a reusable "
                        + "analytic transfer, with no claim of literature priority."))),
                DescribeRole.Theorem))));
}
