using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class AdjointKernelRedundancyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjoint kernel is exactly the space of redundant protocol coefficients.",
        H("Adjoint-Kernel Redundancy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-redundancy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/LinearMemory/AdjointKernelRedundancy."
                        + "adjoint_kernel_redundancy"),
                H("Adjoint-kernel coefficients are exactly vanishing protocol combinations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family ell consist of protocol representatives in a "
                            + "finite-dimensional real Hilbert state space. The analysis map M "
                            + "records the inner product with every representative.")),
                    Paragraph(Text(
                        "For every Euclidean coefficient vector a, the adjoint M-star applied to "
                            + "a is the finite synthesis sum of a_i times ell_i. Consequently a "
                            + "lies in the adjoint kernel exactly when that linear combination "
                            + "vanishes.")),
                    Paragraph(Text(
                        "Thus a protocol-side residual direction need not mean the absence of a "
                            + "state. It records an exact linear dependence among the selected "
                            + "protocol representatives."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("V");
        Formula indexType = F.Id("iota");
        Formula ell = F.Id("ell");
        Formula a = F.Id("a");
        Formula i = F.Id("i");
        Formula observation = F.Id("M");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula euclidean = Call("EuclideanSpace", reals, indexType);
        Formula observationType = Call("LinearMap", reals, state, euclidean);
        Formula representativeFamily = Arrow(indexType, state);
        Formula coordinateFunctional = Lambda(
            i, indexType, Call("innerSL", reals, Apply(ell, i)));
        Formula coordinateMap = Call("linearPi", coordinateFunctional);
        Formula l2Equivalence = Call(
            "withLpLinearEquiv", D(2), reals, Arrow(indexType, reals));
        Formula observationConstruction = Call(
            "comp", Call("toLinearMap", Call("symm", l2Equivalence)), coordinateMap);
        Formula coefficientTerm = Call("smul", Apply(a, i), Apply(ell, i));
        Formula linearCombination = Call(
            "finSum", Lambda(i, indexType, coefficientTerm));
        Formula kernelMembership = Seq(
            a, Sp, InMacro, Sp,
            Call("ker", Call("adjoint", observation)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(state, Comma, Sp, indexType), type), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", state), Comma, Sp,
                Typeclass("InnerProductSpace", reals, state), Comma),
            Seq(
                Grp(), Typeclass("FiniteDimensional", reals, state), Comma, Sp,
                Typeclass("Fintype", indexType), Comma),
            Seq(
                Grp(), Forall, Sp, Typed(ell, representativeFamily), Comma, Sp,
                Typed(a, euclidean), Comma),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(observation, observationType), Sp,
                Eq, Sp, observationConstruction, Semi),
            Seq(
                kernelMembership, Sp, Leftrightarrow, Sp,
                linearCombination, Sp, Eq, Sp, D(0), Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

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
