using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CyclicNearestReturnDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/CyclicNearestReturn",
                "Finite linear orders carry mutually inverse cyclic nearest-return maps."),
            H("Cyclic Nearest Returns"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("cyclic-nearest-return-specification"),
                    H("Cyclic nearest-return specification"),
                    LeanTheorem(
                        "D5/S1/Recurrence/CyclicNearestReturn."
                        + "cyclic_nearest_return_spec"),
                    Disp(Seq(Forall, Sp, F.Id("S"), Subseteq, Alpha, Esc, F.Text, Grp(F.Id("finite")), Comma, Esc, F.Id("S"), Neq, Emptyset, Colon, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, F.Id("x"), Close, InMacro, Sp, F.Id("S"), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("pred")), Underscore, F.Id("S"), Open, F.Id("x"), Close, InMacro, Sp, F.Id("S"), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("pred")), Underscore, F.Id("S"), Open, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, F.Id("x"), Close, Close, Eq, F.Id("x"), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, Operatorname, Grp(F.Id("pred")), Underscore, F.Id("S"), Open, F.Id("x"), Close, Close, Eq, F.Id("x"), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, Sp, F.Id("S"), Comma, Esc, F.Id("x"), Lt, F.Id("y"), Rightarrow, Neg, Thin, Open, F.Id("y"), Lt, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, F.Id("x"), Close, Close, Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, Sp, F.Id("S"), Comma, Esc, F.Id("y"), Lt, F.Id("x"), Rightarrow, Neg, Thin, Open, Operatorname, Grp(F.Id("pred")), Underscore, F.Id("S"), Open, F.Id("x"), Close, Lt, F.Id("y"), Close, Close, Esc, Land, Esc, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, Max, Sp, F.Id("S"), Close, Eq, Min, Sp, F.Id("S"), Esc, Land, Esc, Operatorname, Grp(F.Id("pred")), Underscore, F.Id("S"), Open, Min, Sp, F.Id("S"), Close, Eq, Max, Sp, F.Id("S"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Every nonempty finite subset of a linear order has a cyclic successor "
                        + "and predecessor. Both maps remain in the subset and are mutual "
                        + "inverses there. Away from the boundary they select the nearest point "
                        + "in the requested direction; at the maximum and minimum they wrap "
                        + "explicitly to the opposite endpoint.")))))));
}
