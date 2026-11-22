using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RHSeventhWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHSeventhWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seventh-root correction in RH prime windows",
        H("The signed sixth and seventh terms and the cube-cutoff primitive"),
        Blocks(
            Paragraph(Text("Let R5(a,B) be the signed remainder after the corrections through the fifth root. "
                + "From the integral of max(-Qtheta(x),0)/sqrt(x) on [a,B], subtract 2 log(B/a), the "
                + "ordinary spectral primitive at B minus its value at a, the cube main term "
                + "9 times the negative one-sixth power difference, the square primitive at B minus "
                + "its value at a, and 25/6 times the negative three-tenths power difference. "
                + "Here Qtheta is the prime-only tail.")),
            Paragraph(Text("At a positive cutoff x the cube-cutoff primitive is")),
            new DocumentBlock.DisplayFormula(CubePrimitive()),
            Paragraph(Text("The sum uses every actual nontrivial zero occurrence with full analytic multiplicity.")),
            Describe.Lean(
                DescribeId.Create("seventh-prime-power-window"),
                DeclarationHandle.Create(Owner + ".prime_window_seventh_of_rh"),
                H("The uniform remainder at the three-eighths decay rate"),
                StatementSource.FromAuthor(WindowEstimate()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text("The normalized sixth and seventh corrections have coefficients -6/5 and 7/6. "
                        + "The centered square and cube tails give their spectral densities with errors of order "
                        + "x^(-1/2). The centered fifth tail and the complete-tail residual are also bounded "
                        + "by the three-eighths power majorant.")),
                    Paragraph(Text("Eventual positivity allows the signed prime-only density on the whole common "
                        + "log interval. Integrating the sixth and seventh terms gives the coefficients -18/5 "
                        + "and 49/15. Integrating the cube spectrum gives its oriented primitive difference. "
                        + "The majorant integrates on that same interval, so the error bound vanishes when B = a."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), Real, body);
    private static Formula Compare(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Le(Formula left, Formula right) =>
        Compare(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula CubeAt(Formula x) =>
        F.Seq(new Formula.Subscript(F.Id("A"), F.D(3)), F.Open, x, F.Close);

    private static Formula CubePrimitive()
    {
        var x = F.Id("x");
        var rho = F.Rho;
        var exponent = Subtract(new Formula.Fraction(rho, F.D(3)), new Formula.Fraction(F.D(1), F.D(2)));
        var denominator = Multiply(Multiply(rho, Subtract(F.D(3), rho)),
            Subtract(F.D(3), Multiply(F.D(2), rho)));
        var summand = new Formula.Fraction(new Formula.Power(x, exponent), denominator);
        return F.Disp(Equal(CubeAt(x),
            F.Seq(F.D(1), F.D(8), F.Sp, F.Re, F.Sp, F.Sum, F.Underscore, F.Grp(rho), F.Sp, summand)));
    }

    private static Formula Difference(Formula a, Formula b, Formula numerator, Formula denominator)
    {
        var power = new Formula.Negate(new Formula.Fraction(numerator, denominator));
        return Subtract(new Formula.Power(a, power), new Formula.Power(b, power));
    }

    private static Formula WindowEstimate()
    {
        var a = F.Id("a");
        var b = F.Id("B");
        var t = F.Id("T");
        var k = F.Id("K");
        var residual = F.Seq(new Formula.Subscript(F.Id("R"), F.D(5)), F.Open, a, F.Comma, b, F.Close);
        var sixth = Multiply(new Formula.Fraction(F.Seq(F.D(1), F.D(8)), F.D(5)),
            Difference(a, b, F.D(1), F.D(3)));
        var seventh = Multiply(new Formula.Fraction(F.Seq(F.D(4), F.D(9)), F.Seq(F.D(1), F.D(5))),
            Difference(a, b, F.D(5), F.Seq(F.D(1), F.D(4))));
        var corrected = Subtract(Add(Subtract(Add(residual, sixth), CubeAt(b)), CubeAt(a)), seventh);
        var estimate = Le(new Formula.Absolute(corrected), Multiply(k, Difference(a, b, F.D(3), F.D(8))));
        var admissible = Imp(And(Le(t, a), Le(a, b)), estimate);
        var windows = Bind(FormulaQuantifier.ForAll, "a", Bind(FormulaQuantifier.ForAll, "B", admissible));
        var positive = Compare(F.D(0), FormulaRelationOperator.LessThan, k);
        return F.Disp(Imp(F.Id("RH"), Bind(FormulaQuantifier.Exists, "T",
            Bind(FormulaQuantifier.Exists, "K", And(Le(F.D(2), t), And(positive, windows))))));
    }
}
