using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteColumnGcdNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Bezout elimination of integral sampling columns.",
        H("Finite Integral Column Normalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-integral-column-gcd-normalization"),
            DeclarationHandle.Create("D5/S1/Recurrence/FiniteColumnGcdNormalization.finite_column_gcd_normalization"),
            H("Finite column gcd normalization"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For any coordinate type with decidable equality, a finite set s, a pivot p outside s, "
                + "an integer a and an integer column v, an integer linear automorphism e satisfies the displayed "
                + "formula for every x with x(p)=a and x(i)=v(i) on s. Negative inputs and a zero gcd are included. "
                + "Finite-set induction combines the current pivot and each new coordinate by an invertible "
                + "two-coordinate Bezout transformation. This supplies the integral column reduction needed "
                + "after clearing the first row of a finite Fibonacci sampling matrix."))),
            DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula coordinateType = F.Id("I");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula functions = Seq(coordinateType, Sp, To, Sp, integers);
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula v = F.Id("v");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula j = F.Id("j");

        Formula typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
        Formula parenthesized(Formula value) => Seq(Open, value, Close);
        Formula and(Formula left, Formula right) =>
            Seq(parenthesized(left), Sp, Land, Sp, parenthesized(right));
        Formula implies(Formula premise, Formula conclusion) =>
            Seq(parenthesized(premise), Sp, Rightarrow, Sp, parenthesized(conclusion));
        Formula forall(Formula variable, Formula type, Formula body) =>
            Seq(Forall, Sp, typed(variable, type), Comma, Sp, body);
        Formula exists(Formula variable, Formula type, Formula body) =>
            Seq(Exists, Sp, typed(variable, type), Comma, Sp, body);
        Formula application(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula member(Formula value, Formula set) => Call("mem", value, set);
        Formula absolute(Formula value) => Seq(Vert, Sp, value, Sp, Vert);
        Formula finiteGcd = Call("gcd", absolute(a),
            Call("gcdFinite", s,
                Seq(F.Id("fun"), Sp, j, Sp, Rightarrow, Sp,
                    absolute(application(v, j)))));
        Formula pivotValue = Call("IntCast", finiteGcd);
        Formula piecewise = Call("if", Equal(i, p), pivotValue,
            Call("if", member(i, s), D(0), application(x, i)));
        Formula hypotheses = and(
            Equal(application(x, p), a),
            forall(i, coordinateType,
                implies(member(i, s), Equal(application(x, i), application(v, i)))));
        Formula equality = Equal(
            application(application(F.Id("e"), x), i), piecewise);
        Formula result = exists(F.Id("e"),
            Call("LinearEquiv", integers, functions, functions),
            forall(x, functions, implies(hypotheses,
                forall(i, coordinateType, equality))));
        Formula statement = forall(s, Call("Finset", coordinateType),
            forall(p, coordinateType,
                forall(a, integers,
                    forall(v, functions,
                        implies(
                            Seq(Neg, Sp, member(p, s)),
                            result)))));
        return Disp(forall(coordinateType, F.Id("TypeStar"),
            Seq(Call("DecidableEq", coordinateType), Comma, Sp,
                statement)));
    }
}
