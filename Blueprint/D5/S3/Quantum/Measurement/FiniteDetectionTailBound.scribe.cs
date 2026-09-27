using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteDetectionTailBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/FiniteDetectionTailBound.finite_detection_tail_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional repeated detection has a geometric survival tail above its dark subspace.",
        H("Finite Detection Tail Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-detection-tail-bound"),
            DeclarationHandle.Create(Declaration),
            H("Survival beyond the dark weight has a finite geometric tail"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Q be the no-click operator, let L_x be the finite family of click operators, "
                        + "and let P be the orthogonal projection onto the vectors that never click. "
                        + "Completeness forces survival on the orthogonal complement of that dark "
                        + "space to contract uniformly within one dimension block.")),
                Paragraph(Text(
                    "There is a real gap g strictly between zero and one inclusive. At every block "
                        + "endpoint, the survival operator above P is positive and is bounded in the "
                        + "Loewner order by the corresponding geometric multiple of I-P.")),
                Paragraph(Text(
                    "For every positive semidefinite trace-one matrix supported orthogonally to the "
                        + "dark space, the real survival probabilities form a summable sequence. "
                        + "Their total is at most the dimension divided by g."))),
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

    private static Formula Divide(Formula left, Formula right) =>
        new Formula.Fraction(left, right);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula Adjoint(Formula value) =>
        Seq(value, Caret, Grp(Star));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), x = F.Id("x");
        Formula q = F.Id("Q"), click = F.Id("L"), g = F.Id("g");
        Formula m = F.Id("m"), n = F.Id("N"), rho = F.Id("rho");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = Operator(Grp(F.Id("Type")));
        Formula finD = Call("Fin", d);
        Formula matrix = Call("Matrix", finD, finD, complex);
        Formula identity = Subscript(F.Id("I"), d);
        Formula clickAt = Apply(click, x);
        Formula projection = Call("darkProjection", q, click);

        Formula Survival(Formula time) => Multiply(
            Power(Adjoint(q), time), Power(q, time));
        Formula TraceReal(Formula time) => Call("Re", Call("Tr", Multiply(rho, Survival(time))));

        Formula completeness = Equal(Add(
            Multiply(Adjoint(q), q),
            Seq(Sum, Underscore, Grp(x, Sp, InMacro, Sp, outcomeType), Sp,
                Multiply(Adjoint(clickAt), clickAt))), identity);
        Formula blockTime = Multiply(m, d);
        Formula excess = Subtract(Survival(blockTime), projection);
        Formula geometric = Call("smul", Power(Subtract(D(1), g), m),
            Subtract(identity, projection));
        Formula blockBound = All([Bound("m", nat)], Both(
            LessEqual(D(0), excess), LessEqual(excess, geometric)));
        Formula densityConclusion = Both(
            Call("Summable", Seq(F.Id("N"), Sp, Mapsto, Sp, TraceReal(n))),
            LessEqual(Call("tsum", Seq(F.Id("N"), Sp, Mapsto, Sp, TraceReal(n))),
                Divide(d, g)));
        Formula densityClaim = All([Bound("rho", matrix)],
            Implies(Call("PosSemidef", rho),
            Implies(Equal(Call("Tr", rho), D(1)),
            Implies(Equal(Multiply(projection, rho), D(0)), densityConclusion))));
        Formula conclusion = Exists([Bound("g", real)], Both(
            Less(D(0), g), LessEqual(g, D(1)), blockBound, densityClaim));

        return Disp(All([
            Bound("d", nat), Bound("X", type), Bound("fintype", Call("Fintype", outcomeType)),
            Bound("Q", matrix), Bound("L", Arrow(outcomeType, matrix))],
            Implies(completeness, conclusion)));
    }

    private static Formula Operator(Formula name) => Seq(Operatorname, name);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
