using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class ObserverDistanceClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant leaves are infinitely separated, while cyclic and integer leaves recover their source path distances.",
        H("Observer Distance Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-leaf-observer-distance-classification"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/ObserverDistanceClassification."
                        + "permutation_observer_distance_classification"),
                H("Invariant leaves classify observer distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("I"), Comma, Sp, F.Id("Leaf"), Comma, Esc,
                    Forall, Sp, F.Id("tau"), Sp, InMacro, Sp,
                    Call("EquivPerm", F.Id("I")), Comma, Sp,
                    Forall, Sp, F.Id("leaf"), Sp, InMacro, Sp,
                    Call("Map", F.Id("I"), F.Id("Leaf")), Comma, Sp,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp, InMacro, Sp,
                    F.Id("I"), Comma, Esc,
                    Call("InvariantLeaf", F.Id("tau"), F.Id("leaf")), Sp, Land, Sp,
                    F.Id("leaf"), Open, F.Id("x"), Close, Sp, Neq, Sp,
                    F.Id("leaf"), Open, F.Id("y"), Close, Sp, Rightarrow, Sp,
                    Call("observerDistance", F.Id("tau"), F.Id("x"), F.Id("y")),
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("top")), Sp, Land, Sp,
                    Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp, F.Id("a"), Comma, Sp,
                    F.Id("b"), Sp, InMacro, Sp, Call("ZMod", F.Id("M")), Comma, Esc,
                    Call("windowObserverDistance", F.Id("M"), F.Id("a"), F.Id("b")),
                    Sp, Eq, Sp, Call("windowCycleDist", F.Id("M"), F.Id("a"), F.Id("b")), Sp,
                    Land, Sp,
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Call("orbitConnesDistance", F.Id("m"), F.Id("n")), Sp, Eq, Sp,
                    new Formula.Absolute(Seq(Open, F.Id("n"), Minus, F.Id("m"), Close)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admissible readouts are bounded real functions whose one-step update defect is at most one. An invariant leaf indicator is bounded, unchanged by the update, and separates distinct leaves; scaling it makes the extended supremum infinite.")),
                    Paragraph(Text(
                        "The finite cyclic clause is the exact repository theorem for the window observer distance. The bounded integer clause is the exact orbit Connes distance computation, so both source path metrics are exposed without redefining them.")),
                    Paragraph(Text(
                        "The three clauses are deposited together as the public conjunction required by the source statement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
