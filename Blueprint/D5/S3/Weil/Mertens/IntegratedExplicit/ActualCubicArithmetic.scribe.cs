using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualCubicArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic bound at the actual cubic endpoint",
        H("The arithmetic bound at the actual cubic endpoint"),
        Blocks(Describe.Lean(DescribeId.Create("actual-cubic-arithmetic-lower-bound"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicArithmetic.actual_cubic_arithmetic_lower_bound"),
            H("A lower bound for the normalized weighted Chebyshev error"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write E(x) for Q(x) minus the weighted tail of the Chebyshev "
                    + "error kernel at x divided by r(x). The occurrence rho(k) ranges over "
                    + "both ordinate signs and retains every analytic multiplicity. The masses "
                    + "C3(T) and C2(T) sum inverse cubes through T and inverse squares above T, "
                    + "respectively, with the cutoff on the absolute ordinate.")),
                Paragraph(Text("Logarithmic transport identifies R(b)E(exp(b)) with the integral "
                    + "of W(v)Q(exp(v)) over v > b, where W(v)=(v+2)/v^3 and R(v)=(v+1)/v^2. "
                    + "Use the exact signed explicit formula for Q(exp(v)). Its trivial-zero "
                    + "term contributes nonnegatively. The elementary weight W(v)exp(-v) has "
                    + "primitive -exp(-v)/v^2, which tends to zero, so the constant term "
                    + "integrates to -log(2*pi)exp(-b)/b^2.")),
                Paragraph(Text("The integrated spectral real part is bounded by the norm of "
                    + "the actual spectral tail. Apply the cubic endpoint estimate and divide "
                    + "by R(b)>0 to obtain the stated bound for each positive cutoff satisfying "
                    + "the critical-line premise."))),
            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Claim()
    {
        var b = F.Id("b");
        var cutoff = F.Id("T");
        var k = F.Id("k");
        var lowHeight = Le(new Formula.Absolute(Call("Im", Call("rho", k))), cutoff);
        var onLine = All("k", Natural, Imp(lowHeight,
            new Formula.Relation(Call("Re", Call("rho", k)), FormulaRelationOperator.Equal,
                new Formula.Fraction(D(1), D(2)))));
        var criticalDecay = Call("exp", new Formula.Fraction(new Formula.Negate(b), D(2)));
        var mass = Add(Multiply(criticalDecay, Call("C3", cutoff)),
            new Formula.Fraction(Call("C2", cutoff), cutoff));
        var spectral = Multiply(new Formula.Negate(new Formula.Fraction(Call("W", b), Call("R", b))),
            Seq(Open, mass, Close));
        var elementary = new Formula.Fraction(
            Multiply(Call("log", Multiply(D(2), Pi)), Call("exp", new Formula.Negate(b))),
            Add(b, D(1)));
        var conclusion = Le(Subtract(spectral, elementary), Call("E", Call("exp", b)));
        var positiveCutoff = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, cutoff);
        return Disp(All("b", Real, All("T", Real,
            Imp(Le(Call("log", D(2)), b), Imp(positiveCutoff, Imp(onLine, conclusion))))));
    }
}
