using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class PermaspinTransferEigenvalueOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/dukes2023permaspin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For positive real c and d, the supremum of the real roots of Dukes's cubic dominates c(1-d)^2 and c(1-d^2).",
        H("The largest root of the permaspin cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dukes-cubic"),
                DeclarationHandle.Create(Prefix + "dukesCubic"),
                H("The cubic polynomial"),
                StatementSource.FromAuthor(Disp(CubicFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The polynomial dukesCubic c d is Dukes's t with real coefficients. "
                    + "Polynomial.C embeds a real coefficient as a constant polynomial, and Polynomial.X is the indeterminate. "
                    + "The definition allows every real c and d. The polynomial is monic of degree three. "
                    + "In permaspin.tex, arXiv:2211.08908v3, lines 490-503 introduce c = a^4 and d = b^2 "
                    + "and the two explicit eigenvalues c(1-d)^2 and c(1-d^2); lines 504-509 give this cubic "
                    + "for the other three eigenvalues."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("largest-root"),
                DeclarationHandle.Create(Prefix + "largestRoot"),
                H("The supremum of the real roots"),
                StatementSource.FromAuthor(Disp(LargestRootFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The quantity largestRoot c d is the real supremum of the set of x for which dukesCubic c d evaluates to zero. "
                    + "It expresses the largest-root notion in permaspin.tex line 510 through the supremum operation. "
                    + "This is a total definition for all real parameters; nonemptiness and boundedness of the root set "
                    + "under positive parameters are included in the statement below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The ordering for positive parameters"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of positive real numbers c and d, the cubic has a real root, its real roots are bounded above, "
                    + "and the maximum of their supremum with c(1-d)^2 and c(1-d^2) is that supremum. "
                    + "The nesting of the two maxima is part of the statement. This is the ordering suggested by "
                    + "the numerical observations in permaspin.tex lines 510-513 and used as a hypothesis in line 517. "
                    + "The statement concerns the displayed cubic and the two explicit expressions; "
                    + "it does not assert the transfer-matrix calculation or the subsequent free-energy formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A real root above both explicit expressions"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let c and d be positive real numbers, write t for dukesCubic c d, and put q = c(1+d)^2. "
                        + "The cubic has degree three and leading coefficient one. Expanding at q and collecting terms gives "
                        + "t(q) = -4c^2d^2(d+1)((d+1)(c-1)^2 + 4cd). "
                        + "The inner sum is positive: its first term is nonnegative and 4cd is positive. "
                        + "The remaining factors 4, c^2, d^2 and d+1 are positive, so t(q) < 0.")),
                    Paragraph(Text(
                        "The evaluation of t is continuous, and its positive leading coefficient and positive degree imply "
                        + "that t(x) tends to positive infinity as x tends to positive infinity. "
                        + "The intermediate value theorem on the interval above q, together with t(q) < 0, "
                        + "therefore gives a real r with q < r and t(r) = 0. Since t has positive degree, it is nonzero. "
                        + "Its real roots form a finite set and hence are bounded above.")),
                    Paragraph(Text(
                        "Choose this r. Boundedness of the real root set and membership of r imply "
                        + "r ≤ largestRoot c d by the defining upper-bound property of the supremum. "
                        + "Next, q - c(1-d)^2 = 4cd > 0 and q - c(1-d^2) = 2cd(d+1) > 0. "
                        + "Thus each explicit expression is strictly below q, which is strictly below r, "
                        + "and r is at most largestRoot c d. "
                        + "The root r establishes nonemptiness, and the preceding bound establishes boundedness. "
                        + "Finally, c(1-d)^2 ≤ largestRoot c d reduces the inner maximum to largestRoot c d, "
                        + "and c(1-d^2) ≤ largestRoot c d reduces the outer maximum to the same value."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dukes-2023-permaspin-eigenvalue-order"),
                    ResolutionKind.Proved)))));

    private static Formula CubicFormula()
    {
        Formula c = X("c");
        Formula d = X("d");
        Formula indeterminate = Typed(Qualified("Polynomial", "X"), PolynomialType());
        Formula quadratic = Negate(SumOf(
            Multiply(c, Power(d, D(2))), Power(c, D(2)),
            Multiply(Multiply(Real(2), c), d), c, Real(1)));
        Formula linear = Negate(Multiply(Multiply(c, SumOf(
            Multiply(c, Power(d, D(3))),
            Multiply(Multiply(Real(3), Power(c, D(2))), d),
            Multiply(c, Power(d, D(2))), Power(c, D(2)),
            Multiply(c, d), c, Multiply(Real(3), d), Real(1))), Subtract(d, Real(1))));
        Formula constant = Multiply(Multiply(Multiply(
            SumOf(Power(d, D(2)), Multiply(Real(4), d), Real(1)), Power(c, D(3))),
            Add(d, Real(1))), Power(Subtract(d, Real(1)), D(3)));
        Formula polynomial = SumOf(
            Multiply(Constant(Real(1)), Power(indeterminate, D(3))),
            Multiply(Constant(quadratic), Power(indeterminate, D(2))),
            Multiply(Constant(linear), indeterminate), Constant(constant));
        return ParameterBinders(Equal(Typed(LocalCall("dukesCubic", c, d), PolynomialType()), polynomial));
    }

    private static Formula LargestRootFormula() => ParameterBinders(
        Equal(Typed(LocalCall("largestRoot", X("c"), X("d")), Reals()),
            At(Qualified("sSup"), RootSet())));

    private static Formula ClaimBody()
    {
        Formula largest = LocalCall("largestRoot", X("c"), X("d"));
        Formula fourth = Multiply(X("c"), Power(Subtract(Real(1), X("d")), D(2)));
        Formula fifth = Multiply(X("c"), Subtract(Real(1), Power(X("d"), D(2))));
        Formula ordering = Equal(At(Qualified("max"), At(Qualified("max"), largest, fourth), fifth), largest);
        return ParameterBinders(Implication(Less(Real(0), X("c")),
            Implication(Less(Real(0), X("d")),
                Conjunction(At(Qualified("Set", "Nonempty"), RootSet()),
                    Conjunction(At(Qualified("BddAbove"), RootSet()), ordering)))));
    }

    private static Formula RootSet() => Seq(OpenBrace, Typed(X("x"), Reals()), Sp, Mid, Sp,
        Equal(At(Qualified("Polynomial", "eval"), X("x"), LocalCall("dukesCubic", X("c"), X("d"))), Real(0)),
        CloseBrace);
    private static Formula ParameterBinders(Formula body) => All("c", Reals(), All("d", Reals(), body));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "PermaspinTransferEigenvalueOrder", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Real(byte digit) => Typed(D(digit), Reals());
    private static Formula PolynomialType() => At(Qualified("Polynomial"), Reals());
    private static Formula Constant(Formula coefficient) => At(Qualified("Polynomial", "C"), coefficient);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), Typed(exponent, Naturals()));
    private static Formula SumOf(params Formula[] terms)
    {
        Formula sum = terms[0];
        for (var index = 1; index < terms.Length; index++) sum = Add(sum, terms[index]);
        return sum;
    }
}
