using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class NewtonHankelRealRootCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative real roots of a positive-coefficient polynomial are equivalent to positivity of its Newton--Hankel matrix.",
        H("Newton--Hankel Real-Root Criterion"),
        Blocks(EvaluationNode(), Describe.Lean(
            DescribeId.Create("negative-real-roots-iff-newton-hankel-positive-semidefinite"),
            DeclarationHandle.Create(
                "D5/S3/Constants/NewtonHankelRealRootCriterion."
                    + "negative_real_roots_iff_newtonHankel_posSemidef"),
            H("Negative roots are equivalent to Newton--Hankel positivity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let P be a real polynomial of degree d whose coefficients from degree "
                        + "zero through d are strictly positive. Let lambda enumerate with "
                        + "multiplicity the nonzero roots of q(x)=x^d P(-1/x), and assume its "
                        + "finite support is closed under complex conjugation. Then every root "
                        + "of P is a negative real number if and only if the normalized "
                        + "Newton--Hankel matrix G_d built from the lambda power sums is positive "
                        + "semidefinite.")),
                Paragraph(Text(
                    "The forward direction expands every quadratic form as the normalized sum "
                        + "of squares at real roots. For the reverse direction, a nonreal root "
                        + "and its conjugate are assigned interpolation values i and -i, with "
                        + "zero at every other distinct root. Lagrange interpolation descends to "
                        + "real coefficients and makes the quadratic form strictly negative. "
                        + "Positive coefficients then exclude nonpositive real roots of q, and "
                        + "the reversed-root correspondence gives the negative roots of P.")),
                Paragraph(Text(
                    "This declaration carries only properties one and two of the source theorem. "
                        + "It does not assert a positive-definite determinant realization or a "
                        + "nonnegative-weight Fibonacci-chain realization."))),
            DescribeRole.Theorem))));

    private static DocumentBlock EvaluationNode() => Describe.Lean(
        DescribeId.Create("positive-coefficients-positive-evaluation"),
        DeclarationHandle.Create(
            "D5/S3/Constants/NewtonHankelRealRootCriterion.eval_pos_of_positive_coefficients"),
        H("Positive coefficients give positive evaluation"),
        StatementSource.FromAuthor(Disp(EvaluationFormula())),
        AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(
            "A real polynomial of degree d with strictly positive coefficients from zero through d "
                + "has a strictly positive value at every nonnegative real argument. "
                + "The displayed degree equality and coefficient inequalities are the definition of "
                + "HasPositiveCoefficientsOfDegree. "
                + "Every term in its evaluation sum is nonnegative, and its constant term is strictly positive."))),
        DescribeRole.Theorem);

    private static Formula EvaluationFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula polynomial = ApplyNamed(Named("Polynomial"), reals);
        Formula degree = new Formula.Relation(ApplyNamed(Named("Polynomial", "natDegree"), F.Id("P")),
            FormulaRelationOperator.Equal, F.Id("d"));
        Formula coefficients = Quantify("k", naturals, Implication(
            new Formula.Relation(F.Id("k"), FormulaRelationOperator.LessThanOrEqual, F.Id("d")),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan,
                ApplyNamed(Named("Polynomial", "coeff"), F.Id("P"), F.Id("k")))));
        Formula positive = new Formula.Logic(Parenthesized(degree), FormulaLogicOperator.And,
            Parenthesized(coefficients));
        Formula nonnegative = new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, F.Id("x"));
        Formula evaluation = ApplyNamed(Named("Polynomial", "eval"), F.Id("x"), F.Id("P"));
        Formula conclusion = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, evaluation);
        return Quantify("P", polynomial, Quantify("d", naturals,
            Implication(positive, Quantify("x", reals, Implication(nonnegative, conclusion)))));
    }

    private static Formula Named(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula ApplyNamed(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Quantify(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula polynomial = F.Id("P");
        Formula roots = F.Id("lambda");
        Formula hankel = new Formula.Subscript(F.Id("G"), d);

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, polynomial, Comma, Sp, roots, Comma, RowBreak,
            Open,
            Call("PositiveCoefficientsOfDegree", polynomial, d), Sp, Land, Sp,
            Call("EnumeratesReversedRoots", polynomial, roots), Sp, Land, Sp,
            Call("ConjugationStable", roots),
            Close, Sp, Rightarrow, RowBreak,
            Call("HasOnlyNegativeRealRoots", polynomial), Sp, Iff, Sp,
            Call("PosSemidef", hankel), Dot));
    }
}
