using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class BranchConditionedTraceDistanceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/BranchConditionedTraceDistance."
            + "branch_conditioned_trace_distance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A trace-nonincreasing finite Kraus branch contracts trace distance after weighting by its probability.",
        H("Branch-Conditioned Trace Distance"),
        Blocks(Describe.Lean(
            DescribeId.Create("branch-conditioned-trace-distance"),
            DeclarationHandle.Create(Declaration),
            H("Conditioning is stable above the branch-probability floor"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let rho and sigma be positive semidefinite matrices of trace one. A finite "
                        + "Kraus family defines a completely positive branch whose effect is bounded "
                        + "by the identity, and p and q are its probabilities on the two states.")),
                Paragraph(Text(
                    "The traceless Hermitian state difference splits into positive and negative "
                        + "parts of equal trace. Positivity of the branch and its complementary "
                        + "failure weight bounds both the probability change and the surviving "
                        + "trace-norm change by the original Jordan mass.")),
                Paragraph(Text(
                    "Normalizing the two branch outputs introduces an inverse probability. Weighting "
                        + "by the larger branch probability removes this denominator. A positive "
                        + "probability floor therefore turns an input error epsilon into conditioned "
                        + "error at most epsilon divided by that floor."))),
            DescribeRole.Theorem))));

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Adjoint(Formula value) =>
        Seq(Grp(value), Caret, Grp(Star));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("iota"), index = F.Id("i");
        Formula rho = F.Id("rho"), sigma = F.Id("sigma"), kraus = F.Id("K");
        Formula effect = F.Id("B"), channel = F.Id("Phi");
        Formula p = F.Id("p"), q = F.Id("q"), distance = F.Id("D");
        Formula x = F.Id("X"), y = F.Id("Y");
        Formula pStar = F.Id("pStar"), epsilon = F.Id("epsilon");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula finD = Call("Fin", d);
        Formula matrix = Call("Matrix", finD, finD, complex);
        Formula krausAt = Subscript(kraus, index);
        Formula effectValue = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
            Multiply(Adjoint(krausAt), krausAt));
        Formula channelValue = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
            Multiply(Multiply(krausAt, x), Adjoint(krausAt)));
        Formula probability(Formula state) =>
            Call("Re", Call("Tr", Multiply(state, effect)));
        Formula distanceValue = Divide(Call("traceNorm", Subtract(x, y)), D(2));
        Formula normalized(Formula probabilityValue, Formula state) =>
            Multiply(Divide(D(1), probabilityValue), Apply(channel, state));
        Formula branchDistance = Apply(distance, normalized(p, rho), normalized(q, sigma));
        Formula densityHypotheses = And(
            Call("PosSemidef", rho),
            And(
                Equal(Call("Tr", rho), D(1)),
                And(Call("PosSemidef", sigma), Equal(Call("Tr", sigma), D(1)))));
        Formula branchHypothesis = LessEqual(effectValue, Subscript(F.Id("I"), d));
        Formula firstClause = LessEqual(
            Seq(Lvert, Sp, Subtract(p, q), Sp, Rvert),
            Apply(distance, rho, sigma));
        Formula secondClause = Implies(
            And(Less(D(0), p), Less(D(0), q)),
            LessEqual(
                Multiply(Call("max", p, q), branchDistance),
                Apply(distance, rho, sigma)));
        Formula floorHypotheses = And(
            Less(D(0), pStar),
            And(
                LessEqual(pStar, p),
                And(
                    LessEqual(Apply(distance, rho, sigma), epsilon),
                    Less(epsilon, pStar))));
        Formula floorConclusion = And(
            Less(D(0), q),
            LessEqual(branchDistance, Divide(epsilon, pStar)));
        Formula thirdClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("pStar"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("epsilon"), real)],
            Implies(floorHypotheses, floorConclusion));
        Formula conclusion = And(firstClause, And(secondClause, thirdClause));

        return Disp(Seq(
            Forall, Sp,
            Typed(d, nat), Comma, Sp,
            Typed(indexType, type), Comma, Sp,
            OpenBracket, Call("Fintype", indexType), CloseBracket, Comma,
            RowBreak, Grp(),
            Typed(rho, matrix), Comma, Sp,
            Typed(sigma, matrix), Comma, Sp,
            Typed(kraus, Seq(indexType, Sp, To, Sp, matrix)), Comma,
            RowBreak, Grp(),
            densityHypotheses, Comma, RowBreak, Grp(),
            branchHypothesis, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(effect, matrix), Sp, Eq, Sp, effectValue, Comma,
            RowBreak, Grp(),
            Typed(channel, Seq(matrix, Sp, To, Sp, matrix)), Sp, Eq, Sp,
            x, Sp, Mapsto, Sp, channelValue, Comma,
            RowBreak, Grp(),
            Typed(p, real), Sp, Eq, Sp, probability(rho), Comma, Sp,
            Typed(q, real), Sp, Eq, Sp, probability(sigma), Comma,
            RowBreak, Grp(),
            Typed(distance, Seq(matrix, Sp, To, Sp, matrix, Sp, To, Sp, real)), Sp,
            Eq, Sp, x, Comma, Sp, y, Sp, Mapsto, Sp, distanceValue, Semi,
            RowBreak, Grp(),
            conclusion, Dot));
    }
}
