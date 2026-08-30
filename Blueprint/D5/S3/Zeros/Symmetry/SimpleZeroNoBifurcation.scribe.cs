using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class SimpleZeroNoBifurcationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completed reflection keeps a simple critical-line zero on the line, so an off-line "
            + "birth requires a multiple zero.",
        H("Simple-Zero No-Bifurcation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simple-zero-no-bifurcation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation."
                        + "simple_zero_no_bifurcation"),
                H("A simple reflected zero has no off-line bifurcation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The family parameter is real and the zero coordinate is complex. "
                            + "The public assumptions retain completed reflection, both local "
                            + "partial derivatives, and continuity of their real-linear fields.")),
                    Paragraph(Text(
                        "At a simple critical-line zero, the bivariate implicit-function theorem "
                            + "constructs a unique local zero branch. Reflecting that branch gives "
                            + "another nearby zero branch, so uniqueness makes every nearby zero "
                            + "reflection-fixed and hence critical-line valued.")),
                    Paragraph(Text(
                        "The second public conjunct considers convergent sequences of off-line "
                            + "zeros. Joint continuity supplies the limiting zero; if its complex "
                            + "derivative were nonzero, the first conjunct would put the sequence "
                            + "on the critical line eventually, a contradiction.")),
                    Paragraph(Text(
                        "Repository search found no exact frozen owner. The construction imports "
                            + "the canonical reflection ledger and directly applies Mathlib's "
                            + "bivariate implicit-function theorem and complex-to-real derivative."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ReflectionLedger")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula function = F.Id("F");
        Formula timeDerivative = new Formula.Subscript(F.Id("d"), F.Id("tau"));
        Formula spaceDerivative = new Formula.Subscript(F.Id("d"), F.Id("s"));
        Formula time = F.Id("tau");
        Formula zero = F.Id("s");
        Formula baseTime = new Formula.Subscript(time, D(0));
        Formula baseZero = new Formula.Subscript(F.Id("s"), D(0));
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
        Formula tendsTo(Formula sequence, Formula filter, Formula target) =>
            Call("Tendsto", sequence, filter, neighborhood(target));
        Formula eventually(Formula center, Formula proposition) =>
            Call("EventuallyAt", pair, neighborhood(center), proposition);

        Formula reflection = Seq(
            Forall, Sp, time, InMacro, Sp, real, Comma, Sp,
            zero, InMacro, Sp, complex, Comma, Esc,
            value(time, mirror(zero)), Sp, Eq, Sp,
            Overline, Grp(value(time, zero)));
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
            reflection, Sp, Land, RowBreak, Grp(),
            timeDifferentiability, Sp, Land, Sp,
            spaceDifferentiability, Sp, Land, RowBreak, Grp(),
            timeDerivativeContinuity, Sp, Land, Sp,
            spaceDerivativeContinuity);

        Formula simpleBase = Seq(
            value(baseTime, baseZero), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            ds(baseTime, baseZero), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            realPart(baseZero), Sp, Eq, Sp, critical);
        Formula localLine = eventually(basePair, Seq(
            value(time, zero), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            realPart(zero), Sp, Eq, Sp, critical));
        Formula noBifurcation = Seq(
            Open, simpleBase, Close, Sp, Rightarrow, Sp, localLine);

        Formula timeSequence = new Formula.Subscript(time, F.Id("n"));
        Formula zeroSequence = new Formula.Subscript(F.Id("s"), F.Id("n"));
        Formula sequenceWitness = Seq(
            Exists, Sp,
            Typed(time, Seq(natural, Sp, To, Sp, real)), Comma, Sp,
            Typed(F.Id("s"), Seq(natural, Sp, To, Sp, complex)), Comma, Esc,
            tendsTo(time, Call("atTop", natural), baseTime), Sp, Land, Sp,
            tendsTo(F.Id("s"), Call("atTop", natural), baseZero), Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, F.Id("n"), InMacro, Sp, natural, Comma, Esc,
            value(timeSequence, zeroSequence), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            realPart(zeroSequence), Sp, Neq, Sp, critical);
        Formula offLineBirth = Seq(
            Open,
            realPart(baseZero), Sp, Eq, Sp, critical, Sp, Land, Sp,
            sequenceWitness,
            Close, Sp, Rightarrow, Sp,
            value(baseTime, baseZero), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            ds(baseTime, baseZero), Sp, Eq, Sp, D(0));

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
            Open, noBifurcation, Close, Sp, Land,
            RowBreak, Grp(),
            Open, offLineBirth, Close, Dot));
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
