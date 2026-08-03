using static StrataLint.Scribe.DefinitionDsl;

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
                    LatexStatement.Create(
                        @"Let $S$ be a nonempty finite subset of a linear order. For every "
                        + @"$x\in S$: $$\operatorname{succ}_S(x)\in S,\qquad "
                        + @"\operatorname{pred}_S(x)\in S,\qquad "
                        + @"\operatorname{pred}_S(\operatorname{succ}_S(x))=x,\qquad "
                        + @"\operatorname{succ}_S(\operatorname{pred}_S(x))=x,$$ and for "
                        + @"every $y\in S$: $$x<y\implies\neg\,"
                        + @"(y<\operatorname{succ}_S(x)),\qquad y<x\implies\neg\,"
                        + @"(\operatorname{pred}_S(x)<y).$$ At the endpoints the maps wrap: "
                        + @"$$\operatorname{succ}_S(\max S)=\min S,\qquad "
                        + @"\operatorname{pred}_S(\min S)=\max S.$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Every nonempty finite subset of a linear order has a cyclic successor "
                        + "and predecessor. Both maps remain in the subset and are mutual "
                        + "inverses there. Away from the boundary they select the nearest point "
                        + "in the requested direction; at the maximum and minimum they wrap "
                        + "explicitly to the opposite endpoint.")))))));
}
