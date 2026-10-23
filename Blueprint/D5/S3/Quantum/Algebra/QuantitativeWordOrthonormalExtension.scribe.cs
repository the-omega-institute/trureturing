using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class QuantitativeWordOrthonormalExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common orthonormal extension has small contraction residuals and bounded short-word coefficients.",
        H("Quantitative word orthonormal extension"),
        Blocks(
            Describe.Lean(DescribeId.Create("quantitative-word-orthonormal-extension"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension."
                    + "quantitative_word_orthonormal_extension"),
                H("A threshold-stable extension with word certificates"),
                StatementSource.FromAuthor(Disp(StatementFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let D, r and M be natural numbers with 2 <= r <= D and M <= D squared. "
                        + "Let 0 < delta < 1. On the complex Euclidean space of dimension D, let A be an arbitrary "
                        + "family of M linear contractions and let eta be an arbitrary orthonormal family of r seed vectors. "
                        + "There is an integer r <= m <= D and one orthonormal family e of length m whose first r vectors "
                        + "are eta. In the display, Fin(k) means the indices 0 through k-1, End over C means "
                        + "complex-linear endomorphisms, and the arrow with subscript zero denotes finitely supported functions. "
                        + "Put W = span(e) and let P be its orthogonal projection; P depends on the same e quantified in the display. "
                        + "Seed indices in e are included by the order-preserving inclusion Fin(r) into Fin(m). Every residual A(a)e(j) - "
                        + "P(A(a)e(j)) has norm at most delta, simultaneously for every a and j.")),
                    Paragraph(Text("For this same e, every vector e(j) has a finitely supported complex coefficient "
                        + "family c(j) on pairs (w,b), with w a list of contraction labels and b a seed index. "
                        + "In the display, supp(c(j)) is the finite set of pairs (w,b) with nonzero coefficient, "
                        + "each sum runs over this support, and the absolute-value bars on w denote its length. "
                        + "It satisfies e(j) = sum c(j)(w,b) A(w)eta(b); every supported word has length at most m-r; "
                        + "and sum of the absolute coefficients is at most (D/delta) to the power m-r. "
                        + "The displayed A with word subscript denotes the chronological word operator: the empty word acts "
                        + "as identity, and appending a label a applies A(a) "
                        + "after the existing word. The Lean expression uses the product of the reversed list of endomorphisms.")),
                    Paragraph(Text("To extend a current orthonormal family, take a residual whose norm beta exceeds "
                        + "delta and adjoin its normalization. Orthogonality preserves all preceding vectors. "
                        + "The new vector is beta inverse times A(a)e(j) minus its m orthogonal projection terms. "
                        + "Each projection coefficient has modulus at most one. Transporting the existing finite word "
                        + "certificates therefore increases their word lengths by at most one and multiplies their "
                        + "absolute coefficient bound by at most (m+1)/delta <= D/delta. Dimension limits the number "
                        + "of extensions. At termination every residual meets the threshold.")),
                    Paragraph(Text("The empty contraction family, full initial dimension r=D, repeated or zero "
                        + "contractions and arbitrarily small positive thresholds are included. No singular-value, "
                        + "conditioning or previously successful extension premise is imposed. This conclusion concerns "
                        + "the finite-dimensional contraction geometry and its coefficients."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula domain, Formula body) => Seq(
        Forall, Sp, F.Id(name), Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Ex(string name, Formula domain, Formula body) => Seq(
        Exists, Sp, F.Id(name), Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(
        Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(
        Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(
        left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(
        left, FormulaRelationOperator.Equal, right);
    private static Formula Fin(Formula size) => Call(Named("Fin"), size);
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));

    private static Formula StatementFormula()
    {
        var d = F.Id("D");
        var r = F.Id("r");
        var m = F.Id("m");
        var labels = F.Id("M");
        var delta = F.Id("delta");
        var a = F.Id("a");
        var x = F.Id("x");
        var b = F.Id("b");
        var j = F.Id("j");
        var w = F.Id("w");
        var operators = F.Id("A");
        var eta = F.Id("eta");
        var e = F.Id("e");
        var c = F.Id("c");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var space = new Formula.Power(complex, d);
        var words = Call(Named("List"), Fin(labels));
        var pair = Seq(words, Sp, Times, Sp, Fin(r));
        var coefficients = Seq(Par(pair), Sp, To, Underscore, Grp(D(0)), Sp, complex);
        var endomorphisms = Seq(Sub(Named("End"), complex), Open, space, Close);
        var ej = Call(e, j);
        var cj = Call(c, j);
        var coefficient = Call(cj, w, b);
        var action = Call(Call(operators, a), ej);
        var residual = Seq(action, Minus, Call(F.Id("P"), action));
        var gap = Seq(m, Minus, r);
        var supportIndex = Seq(Open, w, Comma, b, Close, Sp, InMacro, Sp,
            Call(Named("supp"), cj));
        var expansion = Seq(Sum, Underscore, Grp(supportIndex), Sp,
            coefficient, Sp, Sub(operators, w), Sp, Call(eta, b));
        var mass = Seq(Sum, Underscore, Grp(supportIndex), Sp,
            new Formula.Absolute(coefficient));
        var shortWords = All("j", Fin(m), All("w", words, All("b", Fin(r),
            Imp(Seq(coefficient, Sp, Neq, Sp, D(0)),
                Le(new Formula.Absolute(w), gap)))));
        var certificates = Ex("c", new Formula.TypeArrow(Fin(m), Par(coefficients)),
            And(shortWords, And(All("j", Fin(m), Equal(ej, expansion)),
                All("j", Fin(m), Le(mass,
                    new Formula.Power(Par(new Formula.Fraction(d, delta)), gap))))));
        var extension = Ex("m", naturals, And(Le(r, m), And(Le(m, d),
            Ex("e", new Formula.TypeArrow(Fin(m), space),
                And(Call(Sub(Named("Orthonormal"), complex), e),
                    And(All("b", Fin(r), Equal(Call(e, b), Call(eta, b))),
                        And(All("a", Fin(labels), All("j", Fin(m),
                            Le(new Formula.Norm(residual), delta))), certificates)))))));
        var hypotheses = And(Le(D(2), r), And(Le(r, d),
            And(Le(labels, new Formula.Power(d, D(2))),
                And(Seq(D(0), Lt, delta), And(Seq(delta, Lt, D(1)),
                    And(All("a", Fin(labels), All("x", space,
                        Le(new Formula.Norm(Call(Call(operators, a), x)), new Formula.Norm(x)))),
                        Call(Sub(Named("Orthonormal"), complex), eta)))))));
        return All("D", naturals, All("r", naturals, All("M", naturals,
            All("delta", reals,
                All("A", new Formula.TypeArrow(Fin(labels), endomorphisms),
                    All("eta", new Formula.TypeArrow(Fin(r), space),
                        Imp(hypotheses, extension)))))));
    }
}
