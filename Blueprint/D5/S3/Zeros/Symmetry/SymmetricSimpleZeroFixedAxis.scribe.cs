using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class SymmetricSimpleZeroFixedAxisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A symmetric simple zero stays fixed by completed reflection along its unique local continuation.",
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
                        "The statement retains the reflected function family, both local derivative "
                            + "fields, and their continuity assumptions on the real-complex product.")),
                    Paragraph(Text(
                        "The imported simple-zero theorem puts every nearby zero on the critical line. "
                            + "The canonical reflection equivalence then makes each such zero fixed, "
                            + "so both conclusions are public."))),
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
        Formula fixedNearbyZero = eventually(basePair, Seq(
            value(time, zero), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Open,
            mirror(zero), Sp, Eq, Sp, zero, Sp, Land, Sp,
            realPart(zero), Sp, Eq, Sp, critical,
            Close));

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
            Open, simpleBase, Close, Sp, Rightarrow, Sp,
            fixedNearbyZero, Dot));
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
