using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class SharpMeasurementCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint sharp measurements are exactly pairwise commuting, while general effects need not commute.",
        H("Sharp-Measurement Compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-measurements-are-joint-exactly-when-they-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/SharpMeasurementCompatibility."
                        + "sharp_measurement_compatibility"),
                H("Sharp measurements are jointly measurable exactly when they commute"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two arbitrary finite record measurements admit a joint record "
                            + "measurement with the stated marginals exactly when every effect "
                            + "from the first family commutes with every effect from the second.")),
                    Paragraph(Text(
                        "The forward direction expands both marginals and uses orthogonality of "
                            + "distinct joint outcomes. The reverse direction constructs each "
                            + "joint outcome as the product of the commuting effects.")),
                    Paragraph(Text(
                        "The final clauses give one shared positive normalized qubit measurement. "
                            + "Both of its marginals are nonsharp, and their false-false effects "
                            + "do not commute. This records the source's contrast with general "
                            + "nonsharp effects on the same public construction."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula LetDefinition(
        Formula name,
        Formula type,
        Formula value,
        bool terminate = true) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp, name, Colon, Sp, type,
            Sp, Colon, Eq, Sp, value, terminate ? Semi : Comma, Sp);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), outcomeA = F.Id("A"), outcomeB = F.Id("B");
        Formula a = F.Id("a"), b = F.Id("b"), outcome = F.Id("o");
        Formula p = F.Id("P"), q = F.Id("Q"), jointSharp = F.Id("R");
        Formula zPlus = F.Id("zPlus"), zMinus = F.Id("zMinus");
        Formula xPlus = F.Id("xPlus"), xMinus = F.Id("xMinus");
        Formula joint = F.Id("joint"), first = F.Id("first"), second = F.Id("second");
        Formula type = Call("Type");
        Formula boolean = F.Id("Bool");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", n, n, complex);
        Formula qubitState = Call("QubitState");
        Formula qubitMatrix = Call("QubitMatrix");
        Formula boolPair = Seq(boolean, Sp, Times, Sp, boolean);
        Formula sharpJointType = Arrow(Seq(outcomeA, Sp, Times, Sp, outcomeB), matrix);
        Formula effectFamilyA = Arrow(outcomeA, matrix);
        Formula effectFamilyB = Arrow(outcomeB, matrix);
        Formula jointType = Arrow(boolPair, qubitMatrix);
        Formula marginalType = Arrow(boolean, qubitMatrix);
        Formula falseValue = F.Id("false"), trueValue = F.Id("true");

        Formula SharpAt(Formula family) => Call("IsRecordMeasurement", family);
        Formula At(Formula family, params Formula[] arguments) => Apply(family, arguments);
        Formula Pair(Formula left, Formula right) => Call("pair", left, right);
        Formula JointAt(Formula left, Formula right) => At(joint, Pair(left, right));
        Formula Outer(Formula vector) => Call("vecMulVec", vector, Call("star", vector));
        Formula Scale(int numerator, int denominator, Formula value) =>
            Multiply(
                new Formula.Fraction(D((byte)numerator), D((byte)denominator)),
                value);
        Formula SumOver(Formula index, Formula domain, Formula value) =>
            Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, value);

        Formula sharpExists = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("R"),
            sharpJointType,
            And(
                SharpAt(jointSharp),
                And(
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("a"),
                        outcomeA,
                        Equal(
                            At(p, a),
                            SumOver(b, outcomeB, At(jointSharp, Pair(a, b))))),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("b"),
                        outcomeB,
                        Equal(
                            At(q, b),
                            SumOver(a, outcomeA, At(jointSharp, Pair(a, b))))))));

        Formula commute = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", outcomeA), Bound("b", outcomeB)],
            Equal(
                Multiply(At(p, a), At(q, b)),
                Multiply(At(q, b), At(p, a))));

        Formula sharpCriterion = new Formula.Logic(
            sharpExists,
            FormulaLogicOperator.Iff,
            commute);

        Formula zPlusDefinition = LetDefinition(
            zPlus, qubitState, Call("vec2", D(1), D(0)));
        Formula zMinusDefinition = LetDefinition(
            zMinus, qubitState, Call("vec2", D(0), D(1)));
        Formula xPlusDefinition = LetDefinition(
            xPlus, qubitState, Call("vec2", D(1), D(1)));
        Formula xMinusDefinition = LetDefinition(
            xMinus, qubitState, Call("vec2", D(1), Seq(Minus, D(1))));
        Formula jointDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, joint, Colon, Sp, jointType, Comma, Sp,
            Equal(JointAt(falseValue, falseValue), Scale(1, 2, Outer(zPlus))), Comma, Sp,
            Equal(JointAt(falseValue, trueValue), Scale(1, 4, Outer(xPlus))), Comma, Sp,
            Equal(JointAt(trueValue, falseValue), Scale(1, 4, Outer(xMinus))), Comma, Sp,
            Equal(JointAt(trueValue, trueValue), Scale(1, 2, Outer(zMinus))), Semi, Sp);
        Formula firstDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, first, Colon, Sp, marginalType, Comma, Sp,
            Forall, Sp, a, Colon, Sp, boolean, Comma, Sp,
            Equal(At(first, a), SumOver(b, boolean, JointAt(a, b))), Semi, Sp);
        Formula secondDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, second, Colon, Sp, marginalType, Comma, Sp,
            Forall, Sp, b, Colon, Sp, boolean, Comma, Sp,
            Equal(At(second, b), SumOver(a, boolean, JointAt(a, b))), Semi, Sp);

        Formula positive = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("o"),
            boolPair,
            Call("PosSemidef", At(joint, outcome)));
        Formula normalized = Equal(
            SumOver(outcome, boolPair, At(joint, outcome)),
            D(1));
        Formula firstNonsharp = new Formula.Not(SharpAt(first));
        Formula secondNonsharp = new Formula.Not(SharpAt(second));
        Formula noncommuting = NotEqual(
            Multiply(At(first, falseValue), At(second, falseValue)),
            Multiply(At(second, falseValue), At(first, falseValue)));
        Formula contrast = And(
            positive,
            And(normalized, And(firstNonsharp, And(secondNonsharp, noncommuting))));

        Formula assumptions = And(
            SharpAt(p),
            SharpAt(q));
        Formula conclusion = Seq(
            Begin, Grp(F.Id("gathered")),
            assumptions, Sp, Rightarrow, RowBreak, Grp(),
            Open, sharpCriterion, Close, Sp, Land, RowBreak, Grp(),
            zPlusDefinition, RowBreak, Grp(),
            zMinusDefinition, RowBreak, Grp(),
            xPlusDefinition, RowBreak, Grp(),
            xMinusDefinition, RowBreak, Grp(),
            jointDefinition, RowBreak, Grp(),
            firstDefinition, RowBreak, Grp(),
            secondDefinition, RowBreak, Grp(),
            contrast, Dot,
            End, Grp(F.Id("gathered")));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", type), Bound("A", type), Bound("B", type)],
            Seq(
                OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
                OpenBracket, Call("Fintype", outcomeA), CloseBracket, Sp,
                OpenBracket, Call("Fintype", outcomeB), CloseBracket, Comma, Sp,
                Forall, Sp, p, Colon, Sp, effectFamilyA, Comma, Sp,
                q, Colon, Sp, effectFamilyB, Comma, RowBreak, Grp(),
                conclusion)));
    }
}
