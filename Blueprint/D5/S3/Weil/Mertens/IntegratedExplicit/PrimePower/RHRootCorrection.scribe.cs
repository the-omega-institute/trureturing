using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RHRootCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square and cube corrections to the prime-only tail under RH",
        H("The log-density estimate and the two-cutoff error bound"),
        Blocks(
            Paragraph(Text("Write Qtheta for the prime-only tail, D for squareDensity, A(x) for squarePrimitive, "
                + "and W(a,B) for the integral of rootWindowDensity over [log(a),log(B)]. "
                + "The square-cutoff coefficients and occurrence indexing are those of SquareSpectrum.")),
            Describe.Lean(
                DescribeId.Create("rh-prime-power-density"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_prime_power_density"),
                H("The normalized square and cube terms"), StatementSource.FromAuthor(Density()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(Paragraph(Text(
                    "Zhao's equation (14) uses the same prime-only tail. The integrated complete formula "
                    + "bounds the difference between Q and its signed zero contribution by a constant times x^(-1). "
                    + "The centered square transform therefore has error of order x^(-1/2). The normalized "
                    + "cube error has order x^(-1/3) because Q(y) is of order y^(-1/2) at y=x^(1/3). "
                    + "The leading uncentered root terms are 2 and (3/2)x^(-1/6). The fifth-root "
                    + "majorant gives the final x^(-3/10) envelope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("root-window-density"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rootWindowDensity"),
                H("The root correction with the complete-tail residual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At x=exp(u), add the complete normalized tail residual to the square-root-scaled "
                    + "prime-power bias after subtracting its constant main term 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rh-root-correction-window"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_root_correction_window"),
                H("The cube primitive and the shrinking endpoint error"), StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The prime-power bias tends to 2 in the square-root scaling. Under RH the normalized "
                        + "complete tail is eventually bounded in absolute value by firstLiMass plus 1/2, "
                        + "which is strictly below 3/2. These bounds give a strictly positive prime-only "
                        + "density on the whole late half-axis.")),
                    Paragraph(Text(
                        "Integrate the cube term over [log(a),log(B)] to obtain 9(a^(-1/6)-B^(-1/6)). "
                        + "Use the same endpoints for the square primitive and integrate the residual majorant "
                        + "on that interval to retain a^(-3/10)-B^(-3/10). Equal endpoints are included. "
                        + "The statement uses the full actual zero occurrences and requires no independence of ordinates."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Bind(FormulaQuantifier q, string name, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), Real, body);
    private static Formula All(string name, Formula body) => Bind(FormulaQuantifier.ForAll, name, body);
    private static Formula Exists(string name, Formula body) => Bind(FormulaQuantifier.Exists, name, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Lt(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula NegativePower(Formula x, Formula num, Formula den) =>
        F.Seq(x, F.Caret, F.Grp(new Formula.Negate(new Formula.Fraction(num, den))));
    private static Formula CubePower(Formula x) => NegativePower(x, F.D(1), F.D(6));
    private static Formula ErrorPower(Formula x) => NegativePower(x, F.D(3), F.Seq(F.D(1), F.D(0)));

    private static Formula Density()
    {
        var x = F.Id("x");
        var k = F.Id("K");
        var bias = Multiply(Call("sqrt", x), Subtract(Call("Q", x), Call("Qtheta", x)));
        var cube = Multiply(new Formula.Fraction(F.D(3), F.D(2)), CubePower(x));
        var error = Subtract(Subtract(Subtract(bias, F.D(2)), cube), Call("D", Call("log", x)));
        var bound = Le(new Formula.Absolute(error), Multiply(k, ErrorPower(x)));
        return F.Disp(Imp(F.Id("RH"), Exists("K", And(Lt(F.D(0), k),
            All("x", Imp(Le(F.D(8), x), bound))))));
    }

    private static Formula Window()
    {
        var x = F.Id("x");
        var a = F.Id("a");
        var b = F.Id("B");
        var t = F.Id("T");
        var k = F.Id("K");
        var positive = All("x", Imp(Le(t, x),
            Lt(F.D(0), Multiply(Call("sqrt", x), new Formula.Negate(Call("Qtheta", x))))));
        var cube = Multiply(F.D(9), Subtract(CubePower(a), CubePower(b)));
        var error = Add(Subtract(Subtract(Call("W", a, b), cube), Call("A", b)), Call("A", a));
        var estimate = Le(new Formula.Absolute(error), Multiply(k, Subtract(ErrorPower(a), ErrorPower(b))));
        var window = All("a", All("B", Imp(Le(t, a), Imp(Le(a, b), estimate))));
        return F.Disp(Imp(F.Id("RH"), Exists("T", Exists("K", And(Le(F.D(8), t),
            And(Lt(F.D(0), k), And(positive, window)))))));
    }
}
