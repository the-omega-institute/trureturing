using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FiniteDetectionSurvivalLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a complete finite measurement with one no-click operator, the survival effects converge "
            + "to the orthogonal projection onto the vectors that no click can ever detect.",
        H("Single-Kraus Survival Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-detection-dark-space"),
                DeclarationHandle.Create(Prefix + "darkSpace"),
                H("The indefinitely undetected subspace"),
                StatementSource.FromAuthor(DarkSpaceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dark space consists of the vectors annihilated by every click operator "
                        + "after every finite number of no-click steps."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-detection-dark-projection"),
                DeclarationHandle.Create(Prefix + "darkProjection"),
                H("The orthogonal dark-space projection"),
                StatementSource.FromAuthor(DarkProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dark projection is the matrix of the orthogonal projection onto the dark space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-detection-dark-block-contraction"),
                DeclarationHandle.Create(Prefix + "dark_block_contraction"),
                H("Dark-complement survival contracts geometrically by dimension blocks"),
                StatementSource.FromAuthor(DarkBlockContractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Q be the no-click operator and L_x the finite family of click operators. "
                            + "Their adjoint products sum with Q^* Q to the identity. The survival "
                            + "defect above the dark projection is positive, factors through the dark "
                            + "complement, and is controlled by squared norms of restricted powers.")),
                    Paragraph(Text(
                        "Compactness of the unit sphere in the finite-dimensional dark complement "
                            + "turns strict decay after d steps into a uniform positive gap g. Iterating "
                            + "that block contraction bounds the defect at n+kd by (1-g)^k, and the "
                            + "quotient-remainder decomposition gives the corresponding bound at every N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-detection-survival-limit"),
                DeclarationHandle.Create(Prefix + "finite_detection_survival_limit"),
                H("Survival converges exactly to the dark projection"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Q be the no-click operator and let the finite family L_x contain the click "
                            + "operators. Assume that their adjoint products sum with Q^* Q to the identity. "
                            + "The dark space is invariant under Q. On it, Q^*Q is the identity, and finite "
                            + "dimensionality makes the restriction of Q surjective. Consequently the "
                            + "orthogonal complement of the dark space is also invariant under Q.")),
                    Paragraph(Text(
                        "The dimension-step survival defect has the dark space as its kernel. Positivity "
                            + "therefore makes the dimension-step restriction a strict contraction on the "
                            + "orthogonal complement. Compactness of its unit sphere upgrades pointwise "
                            + "strictness to a uniform contraction, whose powers decay geometrically.")),
                    Paragraph(Text(
                        "Survival is the identity on the dark space and tends to zero on its orthogonal "
                            + "complement. Hence the survival matrices converge to the orthogonal dark-space "
                            + "projection. Multiplication by any matrix rho followed by the trace is continuous, "
                            + "which gives the trace limit. Dimension zero is included."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);

    private static Formula Multiply(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

    private static Formula Both(params Formula[] terms) => terms.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula All(Formula.BoundVariable variable, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [variable], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula Power(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));

    private static Formula Adjoint(Formula value) => Seq(value, Caret, Grp(Star));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula NaturalType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MatrixType(Formula d)
    {
        Formula finD = Call("Fin", d);
        return Call("Matrix", finD, finD, ComplexType());
    }

    private static Formula CommonBinders(Formula d, Formula outcomeType, Formula q, Formula click) => Seq(
        Forall, Sp, Typed(d, NaturalType()), Comma, Sp,
        Typed(outcomeType, Seq(Operatorname, Grp(F.Id("Type")))), Comma,
        RowBreak, Grp(),
        Typed(q, MatrixType(d)), Comma, Sp,
        Typed(click, Arrow(outcomeType, MatrixType(d))), Comma, Sp);

    private static Formula DarkSpaceFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), q = F.Id("Q"), click = F.Id("L");
        Formula n = F.Id("n"), x = F.Id("x");
        Formula eventOperator = Multiply(Subscript(click, x), Power(q, n));
        Formula intersection = Call("iInter", Seq(
            n, Sp, InMacro, Sp, NaturalType(), Comma, Sp,
            x, Sp, InMacro, Sp, outcomeType), Call("ker", eventOperator));
        return Disp(Seq(
            CommonBinders(d, outcomeType, q, click),
            Call("darkSpace", q, click), Sp, Eq, Sp, intersection, Dot));
    }

    private static Formula DarkProjectionFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), q = F.Id("Q"), click = F.Id("L");
        Formula projection = Call("starProjection", Call("darkSpace", q, click));
        return Disp(Seq(
            CommonBinders(d, outcomeType, q, click),
            Call("darkProjection", q, click), Sp, Eq, Sp,
            Call("matrix", projection), Dot));
    }

    private static Formula DarkBlockContractionFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), q = F.Id("Q"), click = F.Id("L");
        Formula n = F.Id("n"), k = F.Id("k"), index = F.Id("N"), x = F.Id("x");
        Formula g = F.Id("g"), c = F.Id("c");
        Formula one = D(1), zero = D(0);
        Formula nat = NaturalType(), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula clickAt = Subscript(click, x);
        Formula identity = Subscript(F.Id("I"), d);
        Formula projection = Call("darkProjection", q, click);
        Formula complement = Subtract(identity, projection);
        Formula gap = Subtract(one, g);

        Formula Survival(Formula time) =>
            Multiply(Power(Paren(Adjoint(q)), time), Power(q, time));
        Formula Defect(Formula time) => Subtract(Survival(time), projection);
        Formula Coefficient(Formula time) => Call("c", time);
        Formula ScalarBound(Formula scalar) => Call("smul", scalar, Paren(complement));
        Formula ForIndex(Formula body) => Paren(All(Bound("N", nat), body));
        Formula ForTwo(Formula body) => Paren(new Formula.BindMany(
            FormulaQuantifier.ForAll, [Bound("n", nat), Bound("k", nat)], body));

        Formula completeness = Equal(Add(
            Multiply(Adjoint(q), q),
            Seq(Sum, Underscore, Grp(x, Sp, InMacro, Sp, outcomeType), Sp,
                Multiply(Adjoint(clickAt), clickAt))), identity);
        Formula nonzeroDimension = Seq(d, Sp, Neq, Sp, zero);
        Formula blockIndex = Add(n, Multiply(k, d));
        Formula quotientPower = Power(Paren(gap), Call("div", index, d));
        Formula iteratedPower = Power(Paren(gap), k);
        Formula conclusion = Exists(
            [Bound("g", real), Bound("c", Arrow(nat, real))],
            Both(
                Less(zero, g),
                LessEqual(g, one),
                ForIndex(LessEqual(zero, Coefficient(index))),
                ForIndex(LessEqual(Coefficient(index), one)),
                ForIndex(LessEqual(Coefficient(Add(index, d)),
                    Multiply(Paren(gap), Coefficient(index)))),
                ForIndex(LessEqual(projection, Survival(index))),
                ForIndex(Equal(Defect(index),
                    Multiply(Multiply(Paren(complement), Survival(index)), Paren(complement)))),
                LessEqual(zero, Paren(complement)),
                ForIndex(LessEqual(Defect(index), ScalarBound(Coefficient(index)))),
                ForIndex(LessEqual(new Formula.Norm(Defect(index)), Coefficient(index))),
                Equal(gap, Coefficient(d)),
                LessEqual(Defect(d), ScalarBound(Paren(gap))),
                ForTwo(LessEqual(Coefficient(blockIndex), iteratedPower)),
                ForIndex(LessEqual(Coefficient(index), quotientPower)),
                ForTwo(LessEqual(Defect(blockIndex), ScalarBound(iteratedPower))),
                ForIndex(LessEqual(Defect(index), ScalarBound(quotientPower)))));

        return Disp(Seq(
            CommonBinders(d, outcomeType, q, click),
            OpenBracket, Call("Fintype", outcomeType), CloseBracket, Comma,
            RowBreak, Grp(),
            Paren(Both(completeness, nonzeroDimension)), Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), outcomeType = F.Id("X"), q = F.Id("Q"), click = F.Id("L");
        Formula n = F.Id("N"), x = F.Id("x"), rho = F.Id("rho");
        Formula clickAt = Subscript(click, x);
        Formula identity = Subscript(F.Id("I"), d);
        Formula completeness = Seq(
            Multiply(Adjoint(q), q), Sp, Plus, Sp,
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, outcomeType), Sp,
            Multiply(Adjoint(clickAt), clickAt), Sp, Eq, Sp, identity);
        Formula survival = Multiply(Power(Grp(Adjoint(q)), n), Power(q, n));
        Formula projection = Call("darkProjection", q, click);
        Formula survivalLimit = Seq(
            Lim, Underscore, Grp(n, Sp, To, Sp, Infty), Sp,
            survival, Sp, Eq, Sp, projection);
        Formula traceLimit = Seq(
            Lim, Underscore, Grp(n, Sp, To, Sp, Infty), Sp,
            Call("Tr", Multiply(rho, survival)), Sp, Eq, Sp,
            Call("Tr", Multiply(rho, projection)));

        return Disp(Seq(
            CommonBinders(d, outcomeType, q, click),
            OpenBracket, Call("Fintype", outcomeType), CloseBracket, Comma,
            RowBreak, Grp(),
            completeness, Sp, Rightarrow, RowBreak, Grp(),
            survivalLimit, Sp, Land, Sp,
            Forall, Sp, Typed(rho, MatrixType(d)), Comma, Sp,
            traceLimit, Dot));
    }
}
