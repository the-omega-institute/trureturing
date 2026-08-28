using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class ControllabilityGramianReachableRangeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Dynamics/ControllabilityGramianReachableRange."
            + "controllability_gramian_range_eq_reachable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stable ordinary controllability Gramian has exactly the reachable-state range.",
        H("Controllability Gramian Reachable Range"),
        Blocks(Describe.Lean(
            DescribeId.Create("controllability-gramian-range-equals-reachable"),
            DeclarationHandle.Create(Declaration),
            H("The controllability Gramian range is reachable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The controllability Gramian is constructed as the weight-one "
                        + "observability Gramian of the adjoint system, so its terms are "
                        + "the source operators A^k B B-adjoint (A-adjoint)^k. The displayed "
                        + "summability premise is the exact series form of stability.")),
                Paragraph(Text(
                    "The imported ordinary-Gramian theorem identifies its kernel with the "
                        + "all-future adjoint-input kernel. Infinite observability duality "
                        + "turns that kernel into the orthogonal complement of the canonical "
                        + "reachable span; self-adjointness then identifies the range."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula input = F.Id("U");
        Formula update = F.Id("A");
        Formula control = F.Id("B");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula updateType = Call("LinearMap", scalar, state, state);
        Formula controlType = Call("LinearMap", scalar, input, state);
        Formula adjointUpdate = Call("adjoint", update);
        Formula adjointControl = Call("adjoint", control);
        Formula gramianTerm = Call(
            "discountedGramianTerm", adjointUpdate, adjointControl, D(1));
        Formula stability = Call("Summable", gramianTerm);
        Formula gramian = Call("controllabilityGramian", update, control);
        Formula gramianRange = Call("range", Call("toLinearMap", gramian));
        Formula reachable = Call("reachableSubspace", update, control);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, state, Comma, Sp, input), type),
                Comma),
            Seq(
                Grp(), Typeclass("RCLike", scalar), Comma, Sp,
                Typeclass("NormedAddCommGroup", state), Comma),
            Seq(
                Grp(), Typeclass("InnerProductSpace", scalar, state), Comma, Sp,
                Typeclass("FiniteDimensional", scalar, state), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", input), Comma, Sp,
                Typeclass("InnerProductSpace", scalar, input), Comma),
            Seq(
                Grp(), Typeclass("FiniteDimensional", scalar, input), Comma),
            Seq(
                Grp(), Forall, Sp, Typed(update, updateType), Comma, Sp,
                Typed(control, controlType), Comma),
            Seq(
                Grp(), stability, Sp, Rightarrow, Sp,
                gramianRange, Sp, Eq, Sp, reachable, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
