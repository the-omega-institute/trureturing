using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class FerrersCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients";
    private const string Digest = "The coefficients recover the full parameter tuple and enforce the two support cuts.";
    private static readonly Formula Base = F.Id("F");
    private static readonly Formula Extension = F.Id("E");
    private static readonly Formula Smaller = F.Id("K");
    private static readonly Formula Larger = F.Id("L");
    private static readonly Formula B = F.Id("b");
    private static readonly Formula C = F.Id("c");
    private static readonly Formula Basis = F.Id("B");
    private static readonly Formula Parameter = F.Id("p");
    private static readonly Formula Point = F.Id("x");
    private static readonly Formula U = F.Id("u");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula W = F.Id("w");
    private static readonly Formula L = F.Id("l");
    private static readonly Formula K = F.Id("k");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Coefficient recovery and support"), Blocks(
            Node("parameters", "Params", "Parameter space", DescribeRole.Definition, ParameterSpace(),
                "The product is associated to the right. Each factor is the carrier of the corresponding intermediate field."),
            Node("parameter-coefficients", "paramCoefficients",
                "Linear coefficient map", DescribeRole.Definition, CoefficientMap(),
                "The output vector is indexed in order from zero through three. Field inversion is total, so the map is defined even when the determinant vanishes."),
            Node("param-coefficients-injective", "paramCoefficients_injective",
                "Recovery of the five parameters", DescribeRole.Theorem, Injectivity(),
                "The coordinate along the third basis vector separates the last two parameters when the first two basis vectors span L over K."),
            Node("evaluation-on-k", "evaluation_on_K",
                "Evaluation on the first input block", DescribeRole.Theorem, FirstEvaluation(),
                "The degree-three hypothesis makes the third Frobenius iterate act as the identity on K."),
            Node("evaluation-on-b-k", "evaluation_on_bK",
                "Evaluation on the second input block", DescribeRole.Theorem, SecondEvaluation(),
                "Evaluating on b times K uses the nonzero determinant to recover the coefficient of x from the last two parameters."))));

    private static Formula ParameterSpace() =>
        OverFields(false, false, Equal(ParameterType(),
            Seq(Larger, Sp, Times, Sp, Larger, Sp, Times, Sp, Larger, Sp, Times, Sp,
                Larger, Sp, Times, Sp, Smaller)));

    private static Formula CoefficientMap()
    {
        var third = Multiply(new Formula.Power(Group(Determinant()), new Formula.Negate(Num(1))),
            Group(Subtract(Add(Cast(L), Multiply(C, Cast(K))), Multiply(B, Cast(U)))));
        var output = Seq(OpenBracket, Subtract(Cast(U), third), Comma, Sp, Cast(V), Comma, Sp,
            Cast(W), Comma, Sp, third, CloseBracket);
        var signature = Call("LinearMap", Base, ParameterType(),
            new Formula.TypeArrow(Call("Fin", Num(4)), Extension));

        var map = Group(Seq(CoefficientFunction(C), Sp, Colon, Sp, signature));
        return OverFields(true, false, All("b", Extension, All("c", Extension,
            OverCoordinates(Equal(App(map, Tuple()), output)))));
    }

    private static Formula Injectivity()
    {
        var flag = Call("flag", Basis, Num(2));
        var largerOverSmaller = Call("toSubmodule",
            Call("toSubalgebra", Call("extendScalars", Smaller, Larger)));
        return OverFields(true, false, All("b", Extension,
            ImpliesTo(NotEqual(Determinant(), Num(0)), All("B", Call("Basis", Call("Fin", Num(4)), Smaller, Extension),
                ImpliesTo(LeqTo(Smaller, Larger), ImpliesTo(Equal(flag, largerOverSmaller),
                    Call("Injective", CoefficientFunction(App(Basis, Num(2))))))))));
    }

    private static Formula FirstEvaluation()
    {
        var input = Cast(Point);
        var linearTerm = Multiply(Cast(Projection(1)), input);
        return OverFields(true, true, ImpliesTo(DegreeThree(),
            All("b", Extension, All("c", Extension, All("p", ParameterType(), All("x", Smaller,
                Equal(EvaluateAt(input), EvaluationTerms(linearTerm, input))))))));
    }

    private static Formula SecondEvaluation()
    {
        var point = Cast(Point);
        var input = Multiply(B, point);
        var linearTerm = Multiply(Group(Add(Cast(Projection(2, 2, 2, 1)),
            Multiply(C, Cast(Projection(2, 2, 2, 2))))), point);
        return OverFields(true, true, ImpliesTo(DegreeThree(), All("b", Extension, All("c", Extension,
            ImpliesTo(NotEqual(Determinant(), Num(0)), All("p", ParameterType(), All("x", Smaller,
                Equal(EvaluateAt(input), EvaluationTerms(linearTerm, Group(input))))))))));
    }

    private static Formula EvaluationTerms(Formula linearTerm, Formula input) =>
        Add(Add(linearTerm, Multiply(Cast(Projection(2, 1)), new Formula.Power(input, Call("card", Base)))),
            Multiply(Cast(Projection(2, 2, 1)), new Formula.Power(input,
                new Formula.Power(Call("card", Base), Num(2)))));

    private static Formula Projection(params int[] positions) =>
        Seq([Parameter, .. positions.SelectMany(position => new[] { Dot, Num(position) })]);

    private static Formula OverFields(bool finiteBase, bool finiteExtension, Formula body)
    {
        var intermediateField = Call("IntermediateField", Base, Extension);
        var fields = All("K", intermediateField, All("L", intermediateField, body));
        if (finiteExtension)
            fields = WithInstance(Call("Finite", Extension), fields);

        var extension = All("E", F.Id("Type"), WithInstance(Call("Field", Extension),
            WithInstance(Call("Algebra", Base, Extension), fields)));
        return All("F", F.Id("Type"), WithInstance(Call("Field", Base),
            finiteBase ? WithInstance(Call("Fintype", Base), extension) : extension));
    }

    private static Formula OverCoordinates(Formula body) =>
        All("u", Larger, All("v", Larger, All("w", Larger,
            All("l", Larger, All("k", Smaller, body)))));
    private static Formula Tuple() => Seq(Open, U, Comma, Sp, V, Comma, Sp, W, Comma, Sp,
        L, Comma, Sp, K, Close);
    private static Formula ParameterType() => Call("Params", Smaller, Larger);
    private static Formula CoefficientFunction(Formula c) => App(
        Subscript(F.Id("paramCoefficients"), Seq(Smaller, Comma, Larger)), B, c);
    private static Formula EvaluateAt(Formula input) =>
        App(Call("evaluateLinearized", Base, Extension, App(CoefficientFunction(C), Parameter)), input);
    private static Formula Determinant() =>
        Subtract(new Formula.Power(B, new Formula.Power(Call("card", Base), Num(3))), B);
    private static Formula DegreeThree() => Equal(Call("finrank", Base, Smaller), Num(3));
    private static Formula Cast(Formula value) => Group(Seq(value, Sp, Colon, Sp, Extension));
    private static Formula Group(Formula value) => Seq(Open, value, Close);
    private static Formula Subscript(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula WithInstance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LeqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula ImpliesTo(Formula premise, Formula conclusion) =>
        new Formula.Logic(Group(premise), FormulaLogicOperator.Implies, Group(conclusion));

    private static DocumentBlock Node(
        string id, string declaration, string title, DescribeRole role, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
