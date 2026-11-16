using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordAllIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual separable right-maximum series satisfies the source weighted quadratic.",
        H("Actual-Carrier Weighted Quadratic for Separable Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-weighted-quadratic"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic"),
                H("The actual quadratic with singleton and proper-cut terms"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Sp, Eq, Sp,
                    F.Id("z"), Sp, Plus, Sp,
                    F.Id("z"), Sp, Cdot, Sp, Open, D(1), Sp, Plus, Sp,
                    Call("C", F.Id("q")), Close, Sp, Cdot, Sp, F.Id("J"),
                    Sp, Plus, Sp,
                    Call("C", F.Id("q")), Sp, Cdot, Sp, Open, D(1), Sp, Plus, Sp,
                    Call("C", F.Id("q")), Close, Sp, Cdot, Sp,
                    new Formula.Power(F.Id("J"), D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "J is the positive bivariate series whose outer coefficient marks the "
                        + "strict right-maximum count and whose inner coefficient marks length. "
                        + "q is the positive-length counting series of the literal permutations "
                        + "of Fin n avoiding 2413 and 3142. z is the singleton term, and C is "
                        + "the constant-series embedding into the outer PowerSeries.")),
                    Paragraph(Text(
                        "The proof uses the frozen minimum-cut enumeration on the actual carrier. "
                        + "It restricts the block record laws to exact record fibers, combines the "
                        + "opposite-sign transport with the actual Schröder cardinalities, and "
                        + "derives I0(1+q)=q from the scalar Schröder equation. The proper-cut "
                        + "series then satisfies R=C(q)J and the all-avoider series satisfies "
                        + "U=(1+C(q))J, yielding the displayed quadratic.")),
                    Paragraph(Text(
                        "The result is the source-faithful actual-carrier bridge needed before "
                        + "coefficient extraction. It does not by itself prove the arbitrary-index "
                        + "binomial T_r identity, the all-index declining comparisons, the three "
                        + "peak or the complete four-distribution CKZ conclusion. Registration "
                        + "remains paused and no external-problem resolution is claimed here."))),
                DescribeRole.Theorem))));
}
