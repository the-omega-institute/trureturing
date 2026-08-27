using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class AdaptiveSeparationDepthUpperBoundDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound."
            + "adaptive_separation_depth_upper_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair-separating readouts on a finite state quotient construct an identifying "
            + "adaptive protocol tree with worst realized depth at most one less than "
            + "the number of states.",
        H("Adaptive Separation Depth Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("adaptive-separation-depth-upper-bound"),
            DeclarationHandle.Create(Declaration),
            H("Pair separation gives a state-count adaptive depth bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Strong induction on the current finite candidate set chooses a readout "
                    + "separating two candidates. Every realized answer fiber is a strict "
                    + "subset, so recursion identifies that branch within one fewer query "
                    + "than the current candidate count."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("C");
        Formula protocol = F.Id("P");
        Formula answer = F.Id("A");
        Formula readout = F.Id("q");
        Formula tree = F.Id("T");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula selected = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula responseFamily = Grp(Seq(
            Open, Underscore, Colon, Sp, protocol, Close,
            Sp, Mapsto, Sp, answer));
        Formula treeType = Call("PassiveProtocol", protocol, responseFamily);
        Formula run = Call("runPassiveProtocol", readout, tree);
        Formula separation = Seq(
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), state), Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Rightarrow, Sp,
            Exists, Sp, Typed(selected, protocol), Comma, Sp,
            Apply(readout, selected, left), Sp, Neq, Sp,
            Apply(readout, selected, right));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(state, Comma, Sp, protocol, Comma, Sp, answer), type),
                Comma),
            Seq(Grp(), Typeclass("Fintype", state), Comma),
            Seq(
                Forall, Sp,
                Typed(readout, Arrow(protocol, Arrow(state, answer))), Comma),
            Seq(Grp(), Open, separation, Close, Sp, Rightarrow),
            Seq(
                Exists, Sp, Typed(tree, treeType), Comma, Sp,
                Call("Injective", run), Sp, Land),
            Seq(
                Grp(), Forall, Sp, Typed(left, state), Comma, Sp,
                Call("length", Apply(run, left)), Sp, Leq, Sp,
                Call("card", state), Sp, Minus, Sp, D(1), Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
