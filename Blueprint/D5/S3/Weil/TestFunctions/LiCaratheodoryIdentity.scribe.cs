using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LiCaratheodoryIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Li second-difference series is the completed-zeta "
            + "logarithmic derivative and extends meromorphically.",
        H("Li-Caratheodory Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("li-caratheodory-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/TestFunctions/LiCaratheodoryIdentity."
                        + "li_caratheodory_identity"),
                H("Li curvature has its exact logarithmic-derivative continuation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public coefficient carrier is a real sequence with zero initial "
                            + "value, positive first coefficient, and the standard local "
                            + "Keiper-Li generating law for the canonical xi reading.")),
                    Paragraph(Text(
                        "The Caratheodory function is constructed in the statement from the "
                            + "normalized second differences. Shifted HasSum identities give "
                            + "the exact local equality without a Riemann-hypothesis premise.")),
                    Paragraph(Text(
                        "The same public conclusion identifies the right side as a meromorphic "
                            + "continuation on the complex plane punctured at the Mobius pole. "
                            + "It uses the repository's entire xi reading and Mathlib's "
                            + "logarithmic derivative rather than a parallel carrier."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula coefficient = F.Id("lambda");
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        Formula liCaratheodory = F.Id("liCaratheodory");
        Formula continuation = F.Id("continuation");

        Formula Coefficient(Formula index) =>
            Call("complexCast", Apply(coefficient, index));
        Formula mobius = Fraction(D(1), Sub(D(1), z));
        Formula logarithmicDerivative = Call("logDeriv", F.Id("xiReading"), mobius);
        Formula expansionTerm = Mul(
            Coefficient(Add(n, D(1))),
            Power(z, n));
        Formula expansionValue = Fraction(
            logarithmicDerivative,
            Power(Sub(D(1), z), D(2)));
        Formula expansion = Call(
            "Eventually",
            Lambda(z, complex, Call(
                "HasSum",
                Lambda(n, natural, expansionTerm),
                expansionValue)),
            Call("nhds", Call("complex", D(0))));

        Formula zeroValue = Equal(Apply(coefficient, D(0)), D(0));
        Formula firstPositive = LessThan(D(0), Apply(coefficient, D(1)));
        Formula assumptions = And(And(zeroValue, firstPositive), expansion);

        Formula curvatureNumerator = Add(
            Sub(
                Coefficient(Add(n, D(2))),
                Mul(D(2), Coefficient(Add(n, D(1))))),
            Coefficient(n));
        Formula curvatureTerm = Mul(
            Fraction(
                curvatureNumerator,
                Mul(D(2), Coefficient(D(1)))),
            Call("pow", z, Add(n, D(1))));
        Formula curvatureValue = Add(
            D(1),
            Mul(D(2), Tsum(n, natural, curvatureTerm)));
        Formula curvatureDefinition = Let(
            liCaratheodory,
            Arrow(complex, complex),
            Lambda(z, complex, curvatureValue));

        Formula continuationValue = Mul(
            Fraction(D(1), Coefficient(D(1))),
            logarithmicDerivative);
        Formula continuationDefinition = Let(
            continuation,
            Arrow(complex, complex),
            Lambda(z, complex, continuationValue));

        Formula localIdentity = Call(
            "EventuallyEq",
            Call("nhds", Call("complex", D(0))),
            liCaratheodory,
            continuation);
        Formula puncturedPlane = Seq(
            complex, Sp, Setminus, Sp, OpenBrace, D(1), CloseBrace);
        Formula meromorphicContinuation = Call(
            "MeromorphicOn", continuation, puncturedPlane);
        Formula conclusion = And(localIdentity, meromorphicContinuation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, coefficient, Colon, Sp, Arrow(natural, real), Comma,
            RowBreak, Grp(),
            Open, assumptions, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            curvatureDefinition,
            RowBreak, Grp(),
            continuationDefinition,
            RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Let(Formula name, Formula type, Formula value) => Seq(
        Operatorname, Grp(F.Id("let")), Sp,
        name, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Comma);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Tsum(Formula variable, Formula domain, Formula body) => Seq(
        Sum, Underscore, Grp(variable, InMacro, Sp, domain), Sp, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
