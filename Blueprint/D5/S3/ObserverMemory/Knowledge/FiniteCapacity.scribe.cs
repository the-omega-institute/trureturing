using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class FiniteCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite readout knowledge has dimension equal to the number of realized classes.",
        H("Finite Knowledge Capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-knowledge-capacity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Knowledge/FiniteCapacity."
                    + "finite_knowledge_capacity"),
                H("Finite knowledge capacity counts realized readout classes"),
                StatementSource.FromAuthor(CapacityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X, Y0, and Y1 be finite types. A complex-valued world observable "
                            + "belongs to the knowledge space of q exactly when it is constant "
                            + "on every q-fiber, equivalently when it factors through q.")),
                    Paragraph(Text(
                        "The pullback from all complex functions on the realized range of q is "
                            + "injective and has exactly that knowledge space as its range. Its "
                            + "dimension is therefore the cardinality of the realized range.")),
                    Paragraph(Text(
                        "If q1 is obtained from q0 by a further readout map, the induced map from "
                            + "the realized q0 range onto the realized q1 range is surjective. "
                            + "Thus the later dimension cannot increase, and the dimension loss "
                            + "is the difference of the two realized-range cardinalities.")),
                    Paragraph(Text(
                        "Loogle and pinned Mathlib returned exact hits "
                            + "LinearMap.finrank_range_of_inj, "
                            + "Module.finrank_fintype_fun_eq_card, "
                            + "Fintype.card_le_of_surjective, and Function.FactorsThrough. "
                            + "The Lean proof applies all four; no exact complete capacity theorem "
                            + "was found in Mathlib or the repository."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Knowledge(Formula readout) =>
        Call("K", readout);

    private static Formula Dimension(Formula readout) => Seq(
        Operatorname, Grp(F.Id("dim")), Underscore, Grp(F.Id("C")), Sp,
        Knowledge(readout));

    private static Formula RangeCard(Formula readout) => Seq(
        Lvert, Call("range", readout), Rvert);

    private static Formula CapacityFormula()
    {
        Formula world = F.Id("X");
        Formula earlyView = Subscript(F.Id("Y"), D(0));
        Formula lateView = Subscript(F.Id("Y"), D(1));
        Formula early = Subscript(F.Id("q"), D(0));
        Formula late = Subscript(F.Id("q"), D(1));
        Formula forget = F.Id("h");

        return Disp(Seq(
            Forall, Sp, world, Comma, Sp, earlyView, Comma, Sp, lateView,
            Comma, Sp, early, Comma, Sp, late, Comma, Sp, forget, Comma, Esc,
            Open,
            Call("Finite", world), Sp, Land, Sp,
            Call("Finite", earlyView), Sp, Land, Sp,
            Call("Finite", lateView), Sp, Land, Sp,
            late, Sp, Eq, Sp, forget, Sp, Circ, Sp, early,
            Close, Sp, Rightarrow, RowBreak,
            Open,
            Dimension(early), Sp, Eq, Sp, RangeCard(early), Sp, Land, RowBreak,
            Dimension(late), Sp, Eq, Sp, RangeCard(late), Sp, Land, RowBreak,
            Dimension(late), Sp, Le, Sp, Dimension(early), Sp, Land, RowBreak,
            Dimension(early), Sp, Minus, Sp, Dimension(late), Sp, Eq, Sp,
            RangeCard(early), Sp, Minus, Sp, RangeCard(late),
            Close, Dot));
    }
}
