using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DualGramVisibleRangesDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Linear/DualGramVisibleRanges.dual_gram_visible_ranges";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two Gram operators of a finite protocol family expose its two visible ranges.",
        H("Dual Gram Visible Ranges"),
        Blocks(Describe.Lean(
            DescribeId.Create("dual-gram-visible-ranges"),
            DeclarationHandle.Create(Declaration),
            H("The state and protocol visible ranges are adjoint duals"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let an indexed family assign a scalar linear readout to every protocol. "
                        + "The observation map is constructed coordinatewise by the canonical "
                        + "linear-map product constructor.")),
                Paragraph(Text(
                    "The state Gram operator is the adjoint followed by the observation map, "
                        + "while the protocol Gram operator uses the reverse composition. "
                        + "Their ranges are respectively the adjoint range and the realizable "
                        + "observation range.")),
                Paragraph(Text(
                    "The proof directly applies the pinned library's two exact finite-dimensional "
                        + "adjoint-composition range lemmas."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula index = F.Id("iota");
        Formula readout = F.Id("ell");
        Formula observation = F.Id("M");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula indexToScalar = Arrow(index, scalar);
        Formula functional = Call("LinearMap", scalar, state, scalar);
        Formula protocolSpace = Call("PiLp", D(2), indexToScalar);
        Formula observationType = Call("LinearMap", scalar, state, protocolSpace);
        Formula readoutType = Arrow(index, functional);
        Formula adjoint = Call("adjoint", observation);
        Formula stateGram = Call("comp", adjoint, observation);
        Formula protocolGram = Call("comp", observation, adjoint);
        Formula coordinateMap = Call("linearPi", readout);
        Formula l2Equivalence = Call(
            "withLpLinearEquiv", D(2), scalar, indexToScalar);
        Formula observationConstruction = Call(
            "comp", Call("toLinearMap", Call("symm", l2Equivalence)), coordinateMap);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, state, Comma, Sp, index), type),
                Comma),
            Seq(
                Grp(), Typeclass("RCLike", scalar), Comma, Sp,
                Typeclass("NormedAddCommGroup", state), Comma, Sp,
                Typeclass("InnerProductSpace", scalar, state), Comma),
            Seq(
                Grp(), Typeclass("FiniteDimensional", scalar, state), Comma, Sp,
                Typeclass("Fintype", index), Comma),
            Seq(
                Forall, Sp, Typed(readout, readoutType), Comma),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(observation, observationType), Sp,
                Eq, Sp, observationConstruction, Semi),
            Seq(
                Call("range", stateGram), Sp, Eq, Sp, Call("range", adjoint),
                Sp, Land),
            Seq(
                Grp(), Call("range", protocolGram), Sp, Eq, Sp,
                Call("range", observation), Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

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
