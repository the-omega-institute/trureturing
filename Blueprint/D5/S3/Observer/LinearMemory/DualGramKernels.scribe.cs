using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class DualGramKernelsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/DualGramKernels.dual_gram_kernels";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two Gram kernels equal the observation and adjoint kernels.",
        H("Dual Gram Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dual-gram-kernels"),
                DeclarationHandle.Create(Declaration),
                H("The state and protocol Gram kernels are exact"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite indexed family assign a scalar linear readout to every "
                            + "protocol. The observation map is constructed coordinatewise on the "
                            + "same square-summable protocol carrier as the visible-range companion.")),
                    Paragraph(Text(
                        "The kernel of the adjoint-observation composition is exactly the unseen "
                            + "state kernel. Reversing the composition gives exactly the kernel of "
                            + "the adjoint, which records redundant protocol combinations.")),
                    Paragraph(Text(
                        "Both clauses directly apply the pinned library's exact finite-dimensional "
                            + "adjoint-composition kernel lemmas."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/LinearMemory/DualGramVisibleRanges")),
        ]));

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
                Call("ker", stateGram), Sp, Eq, Sp, Call("ker", observation),
                Sp, Land),
            Seq(
                Grp(), Call("ker", protocolGram), Sp, Eq, Sp,
                Call("ker", adjoint), Dot),
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
