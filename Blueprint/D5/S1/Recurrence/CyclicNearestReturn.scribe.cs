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
                new DocumentBlock.Describe(
                    DescribeId.Create("cyclic-nearest-return-specification"),
                    DescribeKind.Theorem,
                    H("Cyclic nearest-return specification"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Recurrence/CyclicNearestReturn."
                        + "cyclic_nearest_return_spec")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Every nonempty finite subset of a linear order has a cyclic successor "
                        + "and predecessor. Both maps remain in the subset and are mutual "
                        + "inverses there. Away from the boundary they select the nearest point "
                        + "in the requested direction; at the maximum and minimum they wrap "
                        + "explicitly to the opposite endpoint."))),
                    LatexStatement.Create(
                        @"$$\operatorname{pred}_S(\operatorname{succ}_S(x))=x,\qquad "
                        + @"\operatorname{succ}_S(\operatorname{pred}_S(x))=x,\qquad "
                        + @"\operatorname{succ}_S(\max S)=\min S,\qquad "
                        + @"\operatorname{pred}_S(\min S)=\max S.$$")))));
}
