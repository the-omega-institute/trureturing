using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermWindowZeroCriterionDocument
    : IScribeDocumentDefinition
{
    private const string OnLineDeclaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion."
            + "golden_window_zero_on_line_of_rh";

    private const string ConverseDeclaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion."
            + "golden_window_zero_right_half_strip_converse";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RH confines golden-window zeros away from the residual zero set, with a "
            + "conditional right-half-strip converse.",
        H("Golden Germ Window Zero Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-window-zero-on-line-of-rh"),
                DeclarationHandle.Create(OnLineDeclaration),
                H("RH confines surviving window zeros to the pulled-back critical line"),
                StatementSource.FromAuthor(OnLineFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The residual function G is arbitrary. Assuming the Riemann "
                            + "hypothesis, a zero of the displayed continued product in "
                            + "the open golden window lies on the pulled-back critical "
                            + "line whenever G is nonzero at that point.")),
                    Paragraph(Text(
                        "The proof isolates the zeta factors. The phi-squared factor "
                            + "uses the frozen nontrivial-zero critical-line theorem; "
                            + "the remaining factors are excluded by the strict window "
                            + "bounds and Mathlib's zeta nonvanishing theorem.")),
                    Paragraph(Text(
                        "This conditional statement does not specialize G to the frozen "
                            + "third-order residual and does not establish the Riemann "
                            + "hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-window-zero-right-half-strip-converse"),
                DeclarationHandle.Create(ConverseDeclaration),
                H("Window confinement conditionally excludes right-half-strip zeros"),
                StatementSource.FromAuthor(ConverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here again G is arbitrary. The hResidual premise is an explicit "
                            + "unknown hypothesis: it requires G to survive at every "
                            + "pulled-back zeta zero in the right half of the critical "
                            + "strip.")),
                    Paragraph(Text(
                        "Given that premise and the displayed window-confinement "
                            + "implication, scaling a hypothetical right-half-strip zero "
                            + "by one over phi squared produces a window zero. Confinement "
                            + "then forces the original real part to equal one half, a "
                            + "contradiction.")),
                    Paragraph(Text(
                        "Because hResidual remains unknown, this theorem is only a "
                            + "conditional converse. It claims no progress toward proving "
                            + "the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula OnLineFormula()
    {
        Formula complex = ComplexNumbers();
        Formula g = F.Id("G");
        Formula s = F.Id("s");
        Formula hypotheses = Implies(
            LowerWindow(s),
            Implies(
                UpperWindow(s),
                Implies(
                    Equal(GermProduct(g, s), D(0)),
                    Implies(
                        NotEqual(Apply(g, s), D(0)),
                        Equal(RealPart(s), CriticalLine())))));
        Formula quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("G", Arrow(complex, complex)), Bound("s", complex)],
            hypotheses);

        return Disp(Implies(F.Id("RiemannHypothesis"), quantified));
    }

    private static Formula ConverseFormula()
    {
        Formula complex = ComplexNumbers();
        Formula g = F.Id("G");
        Formula rho = F.Id("rho");
        Formula s = F.Id("s");
        Formula residual = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex)],
            Implies(
                Equal(Zeta(rho), D(0)),
                Implies(
                    Less(Half(), RealPart(rho)),
                    Implies(
                        Less(RealPart(rho), D(1)),
                        NotEqual(
                            Apply(g, Divide(rho, PhiSquared())),
                            D(0))))));
        Formula confinement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                LowerWindow(s),
                Implies(
                    UpperWindow(s),
                    Implies(
                        Equal(GermProduct(g, s), D(0)),
                        Implies(
                            NotEqual(Apply(g, s), D(0)),
                            Equal(RealPart(s), CriticalLine()))))));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex)],
            Implies(
                Equal(Zeta(rho), D(0)),
                Implies(
                    Less(Half(), RealPart(rho)),
                    Implies(
                        Less(RealPart(rho), D(1)),
                        F.Id("False")))));
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("G", Arrow(complex, complex))],
            Implies(residual, Implies(confinement, conclusion)));

        return Disp(theorem);
    }

    private static Formula GermProduct(Formula g, Formula s)
    {
        Formula left = Multiply(
            Multiply(
                Multiply(
                    Zeta(Multiply(PhiSquared(), s)),
                    Zeta(Multiply(PhiCubed(), s))),
                Inverse(Zeta(Multiply(Multiply(D(2), PhiSquared()), s)))),
            Multiply(
                Multiply(
                    Inverse(Zeta(Multiply(Multiply(D(2), PhiCubed()), s))),
                    Zeta(Multiply(
                        Add(Multiply(D(2), PhiSquared()), PhiCubed()),
                        s))),
                Apply(g, s)));
        return left;
    }

    private static Formula LowerWindow(Formula s) =>
        Less(Divide(D(1), Multiply(D(2), PhiCubed())), RealPart(s));

    private static Formula UpperWindow(Formula s) =>
        Less(RealPart(s), Divide(D(1), PhiSquared()));

    private static Formula CriticalLine() =>
        Divide(D(1), Multiply(D(2), PhiSquared()));

    private static Formula Half() => Divide(D(1), D(2));

    private static Formula PhiSquared() => new Formula.Power(F.Varphi, D(2));

    private static Formula PhiCubed() => new Formula.Power(F.Varphi, D(3));

    private static Formula Zeta(Formula value) => Call("riemannZeta", value);

    private static Formula RealPart(Formula value) => F.Seq(F.Re, F.Grp(value));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Inverse(Formula value) =>
        new Formula.Power(value, F.Seq(F.Minus, D(1)));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));
}
