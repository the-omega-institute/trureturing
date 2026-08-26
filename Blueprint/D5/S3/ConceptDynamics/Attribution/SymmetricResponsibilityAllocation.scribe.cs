using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class SymmetricResponsibilityAllocationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Attribution/SymmetricResponsibilityAllocation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized equivariant allocation is uniform at a fully symmetric event.",
        H("Symmetric Responsibility Allocation"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetric-responsibility-is-uniform"),
            DeclarationHandle.Create(
                DeclarationPrefix + "symmetric_responsibility_is_uniform"),
            H("Symmetry forces equal responsibility"),
            StatementSource.FromAuthor(UniformAllocationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Equivariance and complete symmetry first make the allocation invariant "
                    + "under every relabeling. Swaps then identify every pair of coordinates, "
                    + "and normalization fixes their common value at one divided by the "
                    + "number of labels."))),
            DescribeRole.Theorem))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula FiniteSubjects(Formula size) =>
        Call("Fin", size);

    private static Formula Permutations(Formula size) =>
        Call("Perm", FiniteSubjects(size));

    private static Formula UniformAllocationFormula()
    {
        Formula size = F.Id("n");
        Formula eventType = F.Id("Event");
        Formula action = F.Id("act");
        Formula allocation = F.Id("allocation");
        Formula eventValue = F.Id("event");
        Formula otherEvent = Seq(eventValue, Apos);
        Formula permutation = F.Id("sigma");
        Formula index = F.Id("i");
        Formula realNumbers = Seq(Mathbb, Grp(F.Id("R")));
        Formula subjects = FiniteSubjects(size);

        Formula allocationAtEvent(Formula subject) =>
            Call("allocation", eventValue, subject);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, size, Colon, Sp, NaturalNumbers(), Comma, Sp,
            eventType, Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            action, Colon, Sp,
            Arrow(Permutations(size), Arrow(eventType, eventType)), Comma, RowBreak, Grp(),
            allocation, Colon, Sp,
            Arrow(eventType, Arrow(subjects, realNumbers)), Comma, Sp,
            eventValue, Colon, Sp, eventType, Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, index, Colon, Sp, subjects, Comma, Sp,
            D(0), Sp, Leq, Sp, allocationAtEvent(index),
            Close, Sp, Land, Sp, RowBreak, Grp(),
            Sum, Underscore, Grp(index, Colon, subjects), Sp,
            allocationAtEvent(index), Sp, Eq, Sp, D(1), Sp, Land, Sp, RowBreak, Grp(),
            Open,
            Forall, Sp, permutation, Colon, Sp, Permutations(size), Comma, Sp,
            otherEvent, Colon, Sp, eventType, Comma, Sp,
            index, Colon, Sp, subjects, Comma, Sp,
            Call(
                "allocation",
                Seq(action, Open, permutation, Comma, Sp, otherEvent, Close),
                Seq(permutation, Open, index, Close)),
            Sp, Eq, Sp, Call("allocation", otherEvent, index),
            Close, Sp, Land, Sp, RowBreak, Grp(),
            Call("IsCompletelySymmetric", action, eventValue),
            Rightarrow, Sp, RowBreak, Grp(),
            Open,
            Open,
            Forall, Sp, permutation, Colon, Sp, Permutations(size), Comma, Sp,
            index, Colon, Sp, subjects, Comma, Sp,
            allocationAtEvent(Seq(permutation, Open, index, Close)), Sp, Eq, Sp,
            allocationAtEvent(index),
            Close, Sp, Land, Sp, RowBreak, Grp(),
            Open,
            Forall, Sp, index, Colon, Sp, subjects, Comma, Sp,
            allocationAtEvent(index), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(size),
            Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
