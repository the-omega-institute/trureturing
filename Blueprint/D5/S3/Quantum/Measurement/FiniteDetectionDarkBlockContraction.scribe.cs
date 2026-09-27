using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteDetectionDarkBlockContractionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/FiniteDetectionDarkBlockContraction.dark_block_contraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The no-click survival operators factor through the dark complement, where one dimension "
            + "block is uniformly contractive.",
        H("Finite Detection Dark-Block Contraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-detection-dark-block-contraction"),
            DeclarationHandle.Create(Declaration),
            H("Dark-complement survival contracts within one dimension block"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Q be the no-click operator and L_x the finite family of click operators. "
                        + "Their adjoint products sum with Q^* Q to the identity. Write D for the "
                        + "vectors never detected and P for the orthogonal projection onto D.")),
                Paragraph(Text(
                    "The squared norms of powers of the restriction of Q to the orthogonal "
                        + "complement of D define coefficients c_N between zero and one. Every "
                        + "survival operator dominates P, and its excess over P factors through "
                        + "the complementary projection, has norm at most c_N, and is bounded by "
                        + "c_N(I-P).")),
                Paragraph(Text(
                    "Compactness of the unit sphere in the finite-dimensional dark complement "
                        + "turns pointwise strict decay after d steps into a uniform gap g. Thus "
                        + "one block of survival above P is bounded by (1-g)(I-P)."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Both(params Formula[] terms) => terms.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula Adjoint(Formula value) =>
        Seq(Grp(value), Caret, Grp(Star));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), x = F.Id("x");
        Formula q = F.Id("Q"), click = F.Id("L"), g = F.Id("g"), c = F.Id("c");
        Formula n = F.Id("N");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = Operator(Grp(F.Id("Type")));
        Formula finD = Call("Fin", d);
        Formula matrix = Call("Matrix", finD, finD, complex);
        Formula identity = Subscript(F.Id("I"), d);
        Formula clickAt = Apply(click, x);
        Formula projection = Call("darkProjection", q, click);
        Formula complement = Subtract(identity, projection);

        Formula Survival(Formula time) => Multiply(
            Power(Adjoint(q), time), Power(q, time));

        Formula completeness = Equal(Add(
            Multiply(Adjoint(q), q),
            Seq(Sum, Underscore, Grp(x, Sp, InMacro, Sp, outcomeType), Sp,
                Multiply(Adjoint(clickAt), clickAt))), identity);
        Formula domination = All([Bound("N", nat)],
            LessEqual(projection, Survival(n)));
        Formula factorization = All([Bound("N", nat)],
            Equal(Subtract(Survival(n), projection),
                Multiply(Multiply(complement, Survival(n)), complement)));
        Formula complementPositive = LessEqual(D(0), complement);
        Formula coefficientNonnegative = All([Bound("N", nat)],
            LessEqual(D(0), Apply(c, n)));
        Formula coefficientBounded = All([Bound("N", nat)],
            LessEqual(Apply(c, n), D(1)));
        Formula coefficientRecurrence = All([Bound("N", nat)],
            LessEqual(Apply(c, Add(n, d)),
                Multiply(Subtract(D(1), g), Apply(c, n))));
        Formula powerContraction = All([Bound("N", nat)],
            LessEqual(Subtract(Survival(n), projection),
                Call("smul", Apply(c, n), complement)));
        Formula normContraction = All([Bound("N", nat)],
            LessEqual(new Formula.Norm(Subtract(Survival(n), projection)), Apply(c, n)));
        Formula gapIdentity = Equal(Subtract(D(1), g), Apply(c, d));
        Formula blockContraction = LessEqual(
            Subtract(Survival(d), projection),
            Call("smul", Subtract(D(1), g), complement));
        Formula conclusion = Exists(
            [Bound("g", real), Bound("c", Arrow(nat, real))],
            Both(
                Less(D(0), g),
                LessEqual(g, D(1)),
                coefficientNonnegative,
                coefficientBounded,
                coefficientRecurrence,
                domination,
                factorization,
                complementPositive,
                powerContraction,
                normContraction,
                gapIdentity,
                blockContraction));

        return Disp(All([
            Bound("d", nat), Bound("X", type), Bound("fintype", Call("Fintype", outcomeType)),
            Bound("Q", matrix), Bound("L", Arrow(outcomeType, matrix))],
            Implies(Both(completeness, NotEqual(d, D(0))), conclusion)));
    }

    private static Formula Operator(Formula name) => Seq(Operatorname, name);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
