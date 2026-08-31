using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class CayleyMomentTridiagonalFlowDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cayley moments satisfy the tridiagonal positive-scale flow and its "
            + "resolvent-budget specialization.",
        H("Cayley Moment Tridiagonal Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-moment-tridiagonal-flow"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/CayleyMomentTridiagonalFlow."
                        + "tridiagonal_moment_flow"),
                H("Tridiagonal moment flow"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The moments are constructed from the canonical scale-dependent "
                            + "Cayley spectral measure. The inverse first moment is exposed "
                            + "separately so the zero-index convention is public.")),
                    Paragraph(Text(
                        "Evenness identifies the inverse first moment with the first moment. "
                            + "A half-scale resolvent dominates differentiation under the "
                            + "source integral and yields every recurrence coefficient.")),
                    Paragraph(Text(
                        "The last conjunct differentiates the resolvent budget itself and "
                            + "identifies its derivative with the first moment minus mass."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = RealType();
        Formula natural = NaturalType();
        Formula complex = ComplexType();
        Formula source = F.Id("nu");
        Formula a = F.Id("a");
        Formula t = F.Id("t");
        Formula xi = F.Id("xi");
        Formula z = F.Id("z");
        Formula n = F.Id("n");
        Formula moment = F.Id("m");
        Formula inverseFirst = new Formula.Subscript(F.Id("m"), Seq(Minus, D(1)));
        Formula budget = F.Id("R");

        Formula resolvent = Fraction(
            D(1),
            Seq(Square(xi), Sp, Plus, Sp, Square(t)));
        Formula evenness = Seq(
            Call("map", Seq(xi, Colon, Sp, real, Sp, Mapsto, Sp, Minus, Sp, xi), source),
            Sp, Eq, Sp, source);
        Formula integrability = Seq(
            Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Rightarrow, Sp,
            Call("Integrable", Seq(xi, Colon, Sp, real, Sp, Mapsto, Sp, resolvent), source));

        Formula momentDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            moment, Colon, Sp, Arrow(natural, Arrow(real, real)), Sp,
            Colon, Eq, Sp, Open, n, Colon, Sp, natural, Comma, Sp,
            t, Colon, Sp, real, Close, Sp, Mapsto, Sp,
            Call("Re", Call(
                "integral",
                Call("cayleySpectralMeasure", source, t),
                Seq(z, Colon, Sp, complex, Sp, Mapsto, Sp, Power(z, n)))), Comma);
        Formula inverseDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            inverseFirst, Colon, Sp, Arrow(real, real), Sp,
            Colon, Eq, Sp, t, Colon, Sp, real, Sp, Mapsto, Sp,
            Call("Re", Call(
                "integral",
                Call("cayleySpectralMeasure", source, t),
                Seq(z, Colon, Sp, complex, Sp, Mapsto, Sp,
                    Power(z, Grp(Minus, D(1)))))), Comma);
        Formula budgetDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            budget, Colon, Sp, Arrow(real, real), Sp,
            Colon, Eq, Sp, t, Colon, Sp, real, Sp, Mapsto, Sp,
            Call("integral", source,
                Seq(xi, Colon, Sp, real, Sp, Mapsto, Sp, resolvent)), Comma);

        Formula convention = Seq(
            Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Rightarrow, Sp,
            Apply(inverseFirst, t), Sp, Eq, Sp, MomentAt(moment, D(1), t));

        Formula zeroDerivative = Fraction(
            Seq(
                Fraction(Seq(
                    MomentAt(moment, D(1), a), Sp, Plus, Sp,
                    Apply(inverseFirst, a)), D(2)),
                Sp, Minus, Sp, MomentAt(moment, D(0), a)),
            a);
        Formula zeroFlow = Call(
            "HasDerivAt", Apply(moment, D(0)), zeroDerivative, a);

        Formula successorDerivative = Fraction(
            Seq(
                Fraction(Seq(n, Sp, Plus, Sp, D(2)), D(2)),
                Sp, Cdot, Sp, MomentAt(moment, Seq(n, Sp, Plus, Sp, D(2)), a),
                Sp, Plus, Sp,
                Fraction(Seq(Minus, Sp, n), D(2)),
                Sp, Cdot, Sp, MomentAt(moment, n, a),
                Sp, Minus, Sp,
                MomentAt(moment, Seq(n, Sp, Plus, Sp, D(1)), a)),
            a);
        Formula successorFlow = Seq(
            Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
            Call(
                "HasDerivAt",
                Apply(moment, Seq(n, Sp, Plus, Sp, D(1))),
                successorDerivative,
                a));

        Formula budgetDerivative = Fraction(
            Seq(MomentAt(moment, D(1), a), Sp, Minus, Sp, Apply(budget, a)),
            a);
        Formula budgetFlow = Call("HasDerivAt", budget, budgetDerivative, a);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Colon, Sp, Call("Measure", real), Comma,
            RowBreak, Grp(),
            a, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            Open, evenness, Close, Sp, Land,
            RowBreak, Grp(),
            Open, integrability, Close, Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, a, Sp, Rightarrow,
            RowBreak, Grp(),
            momentDefinition,
            RowBreak, Grp(),
            inverseDefinition,
            RowBreak, Grp(),
            budgetDefinition,
            RowBreak, Grp(),
            Open, convention, Close, Sp, Land,
            RowBreak, Grp(),
            Open, zeroFlow, Close, Sp, Land,
            RowBreak, Grp(),
            Open, successorFlow, Close, Sp, Land,
            RowBreak, Grp(),
            Open, budgetFlow, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MomentAt(
        Formula moment,
        Formula index,
        Formula scale) => Apply(moment, index, scale);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Square(Formula value) => Power(value, D(2));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NaturalType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
}
