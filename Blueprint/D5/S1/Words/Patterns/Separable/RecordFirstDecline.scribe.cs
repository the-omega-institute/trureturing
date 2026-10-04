using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordFirstDeclineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All four actual separable record distributions decline from three to four records.",
        H("The First Declining Comparison for Actual Separable Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-four-record-first-decline"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordFirstDecline.actual_four_record_first_decline"),
                H("Every length, with strictness at every length at least three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Call("a", F.Id("s"), F.Id("n"), D(4)), Le,
                    Call("a", F.Id("s"), F.Id("n"), D(3)), Close, Sp, Land, Sp,
                    Open, F.Id("n"), Ge, D(3), Sp, Rightarrow, Sp,
                    Call("a", F.Id("s"), F.Id("n"), D(4)), Lt,
                    Call("a", F.Id("s"), F.Id("n"), D(3)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each natural n, a(s,n,k) denotes one of the four actual record-fiber "
                        + "cardinalities: irreducible right maxima, irreducible left minima, "
                        + "reducible left maxima or reducible right minima. The carrier is the "
                        + "literal permutations of Fin n avoiding 2413 and 3142. Irreducibility "
                        + "requires positive length and no proper direct cut; reducibility "
                        + "requires a proper direct cut. A proper direct cut separates a "
                        + "nonempty prefix with smaller values from a nonempty suffix. "
                        + "The empty permutation belongs to neither positive class. The "
                        + "singleton is irreducible and has one record; the reducible "
                        + "singleton class is empty.")),
                    Paragraph(Text(
                        "A right maximum exceeds every later value, a left maximum exceeds "
                        + "every earlier value, a left minimum is below every earlier value, "
                        + "and a right minimum is below every later value. These comparisons "
                        + "are strict and the record counts are unshifted. The weak comparison "
                        + "holds at all lengths, including zero, one and two. The strict "
                        + "comparison holds for every n>=3, with no generating-function "
                        + "or cardinality-correspondence premise.")),
                    Paragraph(Text(
                        "Minimum-cut reconstruction and the pointwise opposite-sign cut "
                        + "supplier give the actual weighted record quadratic. Its local "
                        + "coefficient extraction gives J4=t^4(1+q)^4(1+5q+5q^2). "
                        + "The existing scalar cardinality supplier identifies q with the "
                        + "positive actual avoider series t*largeSchroderSeries. Using "
                        + "t(1+q)=q(1-q), the actual difference is J3-J4=t^3 F(q), where "
                        + "F(x)=1+4x+2x^2-8x^3-6x^4+11x^5+15x^6+5x^7.")),
                    Paragraph(Text(
                        "Let K(x)=1-2x-x^2. The numerator of (1+x)^2 F'(x)/K(x) "
                        + "is N(x)=4+12x-12x^2-68x^3-17x^4+176x^5+270x^6+160x^7+35x^8. "
                        + "The proof constructs an exact series V with K*V=N. Its coefficients "
                        + "through index eight are 4,20,32,16,47,286,889,2224,5372; "
                        + "every later coefficient is twice the preceding one plus the "
                        + "coefficient two places earlier. Thus V-20x has nonnegative "
                        + "coefficients at every index, by a universal recurrence.")),
                    Paragraph(Text(
                        "The actual scalar q has positive coefficients at every positive "
                        + "index. Differentiating its quadratic gives K(q)q'=(1+q)^2, "
                        + "so the derivative of F(q(t)) is V(q(t)). Its constant coefficient "
                        + "is four; every positive-index coefficient dominates the corresponding "
                        + "coefficient of 20q(t). Formal integration over the rationals and "
                        + "the constant F(0)=1 give strictly positive coefficients at every "
                        + "index of F(q(t)). Multiplication by t^3 gives the actual "
                        + "right-maximum comparison. Direct application of the frozen "
                        + "RecordTransport theorem gives the other three comparisons; "
                        + "its singleton correction is zero at both record indices.")),
                    Paragraph(Text(
                        "The new content is the unbounded positive-composition inference "
                        + "for this actual decline. All auxiliary mathematical steps are "
                        + "local to the single theorem; compiler-generated equations are "
                        + "not additional escape content. This is a partial universal result. "
                        + "The declining comparisons at arbitrary k>=4, the full Motzkin/Newton "
                        + "argument and a global maximum at three remain open. No complete "
                        + "CKZ Conjecture 2 settlement or KPI increment is claimed."))),
                DescribeRole.Theorem))));
}
