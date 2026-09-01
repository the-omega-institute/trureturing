using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LiCurvatureFourierRepresentationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/TestFunctions/LiCurvatureFourierRepresentation."
            + "li_curvature_fourier_representation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Li curvature is the Fourier sequence of its symmetric Cayley "
            + "probability measure.",
        H("Li Curvature Fourier Representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("li-curvature-fourier-representation"),
            DeclarationHandle.Create(Declaration),
            H("Li curvature as a probability-measure Fourier sequence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A normalized distribution of positive ordinates determines the "
                        + "half-scale Cayley phase and its reflection. Their equally "
                        + "weighted pushforwards construct the symmetric circle measure.")),
                Paragraph(Text(
                    "The Li energy is constructed from the reciprocal Cayley weight and "
                        + "the real part of each integral phase power. Its normalized "
                        + "second difference is the corresponding circle moment.")),
                Paragraph(Text(
                    "The Cayley power estimate makes every energy kernel bounded, so the "
                        + "second difference passes through the source integral without an "
                        + "extra moment premise. The symmetric measure has total mass one "
                        + "and supplies every integer Fourier coefficient."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula circle = F.Id("Circle");
        Formula rho = F.Id("rho");
        Formula xi = F.Id("xi");
        Formula z = F.Id("z");
        Formula n = F.Id("n");
        Formula phase = F.Id("phase");
        Formula reflectedPhase = F.Id("reflectedPhase");
        Formula liEnergy = F.Id("liEnergy");
        Formula normalizedLi = F.Id("normalizedLi");
        Formula liCurvature = F.Id("liCurvature");
        Formula curvatureMeasure = F.Id("curvatureMeasure");
        Formula half = Fraction(D(1), D(2));
        Formula phaseAtXi = Apply(phase, xi);

        Formula phaseDefinition = Let(
            phase,
            Arrow(real, circle),
            Lambda(xi, real, Call("cayleyCircle", half, xi)));
        Formula reflectedPhaseDefinition = Let(
            reflectedPhase,
            Arrow(real, circle),
            Lambda(xi, real, Call("pow", phaseAtXi, Grp(Minus, D(1)))));
        Formula energyAtNAndXi = Seq(
            Fraction(
                Seq(D(4), Sp, Cdot, Sp, Power(xi, D(2)), Sp, Plus, Sp, D(1)),
            D(2)),
            Sp, Cdot, Sp,
            Open, D(1), Sp, Minus, Sp,
            Call("Re", Call("pow", phaseAtXi, n)), Close);
        Formula energyDefinition = Let(
            liEnergy,
            Arrow(integer, Arrow(real, real)),
            Lambda(n, integer, Lambda(xi, real, energyAtNAndXi)));
        Formula normalizedDefinition = Let(
            normalizedLi,
            Arrow(integer, real),
            Lambda(
                n,
                integer,
                Call(
                    "integral",
                    rho,
                    Lambda(xi, real, Apply(liEnergy, n, xi)))));
        Formula curvatureAtN = Fraction(
            Seq(
                Apply(normalizedLi, Seq(n, Sp, Plus, Sp, D(1))),
                Sp, Minus, Sp,
                D(2), Sp, Cdot, Sp, Apply(normalizedLi, n),
                Sp, Plus, Sp,
                Apply(normalizedLi, Seq(n, Sp, Minus, Sp, D(1)))),
            D(2));
        Formula curvatureDefinition = Let(
            liCurvature,
            Arrow(integer, real),
            Lambda(n, integer, curvatureAtN));
        Formula measureDefinition = Let(
            curvatureMeasure,
            Call("Measure", circle),
            Seq(
                half, Sp, Cdot, Sp, Call("map", phase, rho),
                Sp, Plus, Sp,
                half, Sp, Cdot, Sp, Call("map", reflectedPhase, rho)));

        Formula probabilityConclusion = Call(
            "IsProbabilityMeasure", curvatureMeasure);
        Formula fourierConclusion = Seq(
            Forall, Sp, n, Colon, Sp, integer, Comma, Sp,
            Call("complexCast", Apply(liCurvature, n)), Sp, Eq, Sp,
            Call(
                "integral",
                curvatureMeasure,
                Lambda(z, circle, Power(z, n))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Colon, Sp, Call("Measure", real), Comma,
            RowBreak, Grp(),
            OpenBracket, Call("IsProbabilityMeasure", rho), CloseBracket,
            Sp, Rightarrow,
            RowBreak, Grp(),
            phaseDefinition,
            RowBreak, Grp(),
            reflectedPhaseDefinition,
            RowBreak, Grp(),
            energyDefinition,
            RowBreak, Grp(),
            normalizedDefinition,
            RowBreak, Grp(),
            curvatureDefinition,
            RowBreak, Grp(),
            measureDefinition,
            RowBreak, Grp(),
            probabilityConclusion, Sp, Land,
            RowBreak, Grp(),
            Open, fourierConclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Let(Formula name, Formula type, Formula value) => Seq(
        Operatorname, Grp(F.Id("let")), Sp,
        name, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Comma);

    private static Formula Lambda(
        Formula variable,
        Formula domain,
        Formula body) =>
        Seq(variable, Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
