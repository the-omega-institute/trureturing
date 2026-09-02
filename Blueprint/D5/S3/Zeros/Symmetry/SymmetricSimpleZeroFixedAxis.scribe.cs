using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class SymmetricSimpleZeroFixedAxisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A symmetric simple zero has a public unique local continuation fixed by completed reflection.",
        H("Symmetric Simple Zero Fixed Axis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-simple-zero-fixed-axis"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/SymmetricSimpleZeroFixedAxis."
                        + "symmetric_simple_zero_fixed_axis"),
                H("A symmetric simple zero remains reflection-fixed"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The statement exposes positive parameter and zero radii together with the "
                            + "implicit-function continuation through the base zero.")),
                    Paragraph(Text(
                        "The continuation is continuous at the base parameter, is the unique zero in "
                            + "the displayed ball, and remains fixed by completed reflection on the "
                            + "whole displayed parameter interval."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula function = F.Id("F");
        Formula timeDerivative = new Formula.Subscript(F.Id("d"), F.Id("tau"));
        Formula spaceDerivative = new Formula.Subscript(F.Id("d"), F.Id("s"));
        Formula time = F.Id("tau");
        Formula zero = F.Id("s");
        Formula baseTime = new Formula.Subscript(time, D(0));
        Formula baseZero = new Formula.Subscript(zero, D(0));
        Formula pair = Grp(time, Comma, Sp, zero);
        Formula basePair = Grp(baseTime, Comma, Sp, baseZero);
        Formula delta = F.Id("delta");
        Formula epsilon = F.Id("epsilon");
        Formula branch = F.Id("rho");
        Formula parameter = F.Id("kappa");
        Formula critical = F.Id("criticalAbscissa");
        Formula continuousLinear = Call("ContinuousLinearMap", real, real, complex);

        Formula functionType = Seq(real, Sp, To, Sp, complex, Sp, To, Sp, complex);
        Formula timeDerivativeType = Seq(
            real, Sp, To, Sp, complex, Sp, To, Sp, continuousLinear);
        Formula spaceDerivativeType = Seq(real, Sp, To, Sp, complex, Sp, To, Sp, complex);

        Formula value(Formula t, Formula z) => Apply(function, t, z);
        Formula dt(Formula t, Formula z) => Apply(timeDerivative, t, z);
        Formula ds(Formula t, Formula z) => Apply(spaceDerivative, t, z);
        Formula realPart(Formula z) => Seq(Re, Open, z, Close);
        Formula mirror(Formula z) => Call("mirror", z);
        Formula branchAt(Formula t) => Apply(branch, t);
        Formula nearParameter = Seq(
            new Formula.Absolute(Seq(parameter, Sp, Minus, Sp, baseTime)),
            Sp, Lt, Sp, delta);
        Formula nearZero(Formula z) => Seq(
            z, Sp, InMacro, Sp, Call("ball", baseZero, epsilon));
        Formula neighborhood(Formula center) => Call("nhds", center);
        Formula eventually(Formula center, Formula proposition) =>
            Call("EventuallyAt", pair, neighborhood(center), proposition);
        Formula reflection = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("tau"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), complex),
            ],
            Seq(
                value(time, mirror(zero)), Sp, Eq, Sp,
                Overline, Grp(value(time, zero))));
        Formula timeDifferentiability = eventually(basePair, Call(
            "HasFDerivAt",
            Call("timeSlice", function, zero),
            dt(time, zero),
            time));
        Formula spaceDifferentiability = eventually(basePair, Call(
            "HasDerivAt",
            Call("spaceSlice", function, time),
            ds(time, zero),
            zero));
        Formula timeDerivativeContinuity = Call(
            "ContinuousAt",
            Seq(pair, Mapsto, dt(time, zero)),
            basePair);
        Formula spaceDerivativeContinuity = Call(
            "ContinuousAt",
            Seq(pair, Mapsto, ds(time, zero), Sp, Call("smul", Call("id", complex))),
            basePair);
        Formula regularity = Seq(
            Open, reflection, Close, Sp, Land, RowBreak, Grp(),
            timeDifferentiability, Sp, Land, Sp,
            spaceDifferentiability, Sp, Land, RowBreak, Grp(),
            timeDerivativeContinuity, Sp, Land, Sp,
            spaceDerivativeContinuity);

        Formula simpleBase = Seq(
            value(baseTime, baseZero), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            ds(baseTime, baseZero), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            mirror(baseZero), Sp, Eq, Sp, baseZero);
        Formula branchLocality = Seq(
            Forall, Sp, Typed(parameter, real), Comma, Sp,
            nearParameter, Sp, Rightarrow, Sp, nearZero(branchAt(parameter)));
        Formula branchZero = Seq(
            Forall, Sp, Typed(parameter, real), Comma, Sp,
            nearParameter, Sp, Rightarrow, Sp,
            value(parameter, branchAt(parameter)), Sp, Eq, Sp, D(0));
        Formula branchUnique = Seq(
            Forall, Sp, Typed(parameter, real), Comma, Sp,
            nearParameter, Sp, Rightarrow, Sp,
            Forall, Sp, Typed(zero, complex), Comma, Sp,
            nearZero(zero), Sp, Rightarrow, Sp,
            value(parameter, zero), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            zero, Sp, Eq, Sp, branchAt(parameter));
        Formula branchFixed = Seq(
            Forall, Sp, Typed(parameter, real), Comma, Sp,
            nearParameter, Sp, Rightarrow, Sp,
            mirror(branchAt(parameter)), Sp, Eq, Sp, branchAt(parameter));
        Formula branchAxis = Seq(
            Forall, Sp, Typed(parameter, real), Comma, Sp,
            nearParameter, Sp, Rightarrow, Sp,
            realPart(branchAt(parameter)), Sp, Eq, Sp, critical);
        Formula continuation = Seq(
            Exists, Sp, Typed(delta, real), Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Land,
            RowBreak, Grp(),
            Exists, Sp, Typed(epsilon, real), Comma, Sp,
            D(0), Sp, Lt, Sp, epsilon, Sp, Land,
            RowBreak, Grp(),
            Exists, Sp, Typed(branch, Seq(real, Sp, To, Sp, complex)), Comma,
            RowBreak, Grp(),
            branchAt(baseTime), Sp, Eq, Sp, baseZero, Sp, Land, Sp,
            Call("ContinuousAt", branch, baseTime), Sp, Land,
            RowBreak, Grp(),
            Open, branchLocality, Close, Sp, Land, RowBreak, Grp(),
            Open, branchZero, Close, Sp, Land, RowBreak, Grp(),
            Open, branchUnique, Close, Sp, Land, RowBreak, Grp(),
            Open, branchFixed, Close, Sp, Land, RowBreak, Grp(),
            Open, branchAxis, Close);

        return Disp(Seq(
            Forall, Sp,
            Typed(function, functionType), Comma, Sp,
            Typed(timeDerivative, timeDerivativeType), Comma, Sp,
            Typed(spaceDerivative, spaceDerivativeType), Comma,
            RowBreak, Grp(),
            baseTime, InMacro, Sp, real, Comma, Sp,
            baseZero, InMacro, Sp, complex, Comma, Esc,
            regularity, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, simpleBase, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            continuation, Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Call(function, arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
