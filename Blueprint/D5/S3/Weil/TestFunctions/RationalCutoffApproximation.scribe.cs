using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class RationalCutoffApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/RationalCutoffApproximation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every even smooth compactly supported complex test can be approximated by two rational "
            + "polynomials under a fixed smooth plateau. The approximation controls both the "
            + "physical zeroth and second L1 derivatives and the complete paired Weil square sum.",
        H("Rational Polynomial Tests with a Fixed Cutoff"),
        Blocks(
            Paragraph(Text("All physical integrals below use Lebesgue measure on the real line. "
                + "D denotes the physical derivative, P(p,x) is the real evaluation of a rational "
                + "polynomial, S(p,x)=(P(p,x)+P(p,-x))/2, and I is the imaginary unit. A WeilTestFunction is even, smooth "
                + "of every finite order, complex valued, and compactly supported.")),
            Describe.Lean(DescribeId.Create("rational-cutoff-real-two-jet"),
                DeclarationHandle.Create(Prefix + "exists_rational_two_jet"),
                H("Simultaneous rational approximation of three jets"),
                StatementSource.FromAuthor(RealJets()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply real Weierstrass approximation to the continuous "
                    + "second derivative. Approximate its finitely many polynomial coefficients "
                    + "by rational numbers, with an error that bounds their weighted sum on the "
                    + "whole interval. Integrate the rational polynomial twice, choosing zero "
                    + "constants, then add rational approximations to f(0) and Df(0). The mean "
                    + "value inequality bounds both accumulated integration errors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rational-cutoff-even-polynomial"),
                DeclarationHandle.Create(Prefix + "rationalEvenPolynomial"),
                H("Even rational polynomial pair"),
                StatementSource.FromAuthor(EvenPolynomial()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real and imaginary components use independently "
                    + "chosen rational polynomials. Reflection averaging makes their combination even."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-cutoff-test"),
                DeclarationHandle.Create(Prefix + "rationalCutoffTest"),
                H("A fixed smooth plateau"),
                StatementSource.FromAuthor(Cutoff()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive natural R, chi(R) is radiusBump(2R), "
                    + "with inner radius R and outer radius 2R. It equals one on [-R,R], "
                    + "vanishes outside [-2R,2R], takes values between zero and one, and is even "
                    + "and smooth. H(R,p,q) is the resulting Weil test. The radius is fixed "
                    + "before the polynomials are chosen."))), DescribeRole.Definition),
            Paragraph(Text("Write J(f)=integral |f| + integral |D(Df)|. For actual zero data Z, "
                + "write W(Z,f) for zeroSum of the convolution square of f, with its canonical "
                + "symmetric convergence proof. Equivalently it is the absolutely convergent "
                + "sum over all distinct nontrivial zeros of m(n) times F(f,gamma(n)) times "
                + "conj(F(f,conj(gamma(n)))); F uses the kernel exp(-i z x). Each m(n) is the "
                + "actual analytic multiplicity.")),
            Describe.Lean(DescribeId.Create("rational-cutoff-physical-density"),
                DeclarationHandle.Create(Prefix + "exists_rational_cutoff_two_jet"),
                H("Density in the physical two-jet seminorm"),
                StatementSource.FromAuthor(Approximation(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Approximate the real and imaginary parts through order "
                    + "two on [-2R,2R], then average each error with its reflection. Multiplication "
                    + "by chi leaves the original supported test unchanged. For the even error a, "
                    + "the second derivative of chi times a is chi'' times a plus twice chi' "
                    + "times a' plus chi times a''. Compactness bounds both derivatives of chi. "
                    + "Integrating the uniform bounds over an interval of length 4R gives J."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rational-cutoff-complete-approximation"),
                DeclarationHandle.Create(Prefix + "exists_rational_cutoff_approximation"),
                H("Approximation of the complete Weil square sum"),
                StatementSource.FromAuthor(Approximation(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The symmetric spectral ball of radius 6 is finite. "
                    + "The rational fourth-moment tail at T=5 proves summability of its entire "
                    + "complement. Together they give a finite full moment M=sum m(n)/(1+Re(gamma(n))^2)^2.")),
                    Paragraph(Text("Let d=g-H. The physical error gives a strip coefficient "
                    + "Cd at most exp(R) times J(d), while Cg is the zeroth-plus-second weighted "
                    + "integral for g. Both transform factors lie in the closed half strip. "
                    + "The difference of their paired products is bounded, after summation, "
                    + "by Cd(2Cg+Cd)M. Choosing the physical tolerance sufficiently small proves "
                    + "the two error inequalities simultaneously.")),
                    Paragraph(Text("The conjugate frequency is retained even for zeros away "
                    + "from the critical line. No critical-line hypothesis, interpolation "
                    + "identity for H, or vanishing residual at an exceptional zero is required. "
                    + "The conclusion gives existence of rational coefficients; it supplies "
                    + "neither an effective degree or denominator bound nor a numerical evaluator."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatPoly => Call("Polynomial", Seq(Mathbb, Grp(F.Id("Q"))));
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula All(params Formula[] formulas) => formulas.Aggregate((a, b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula ForAll(Formula.BoundVariable[] bs, Formula f) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], f);
    private static Formula Some(Formula.BoundVariable[] bs, Formula f) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. bs], f);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Interval(Formula radius) => Call("Icc", new Formula.Negate(radius), radius);
    private static Formula Support(Formula f, Formula radius) =>
        Rel(Call("tsupport", f), FormulaRelationOperator.SubsetOf, Interval(radius));

    private static Formula RealJets()
    {
        Formula f = F.Id("f"), r = F.Id("B"), e = F.Id("e"), p = F.Id("p"), x = F.Id("x");
        Formula df = Call("D", f), dp = Call("derivative", p);
        Formula BoundJet(Formula function, Formula poly) => Le(
            new Formula.Norm(Sub(At(function, x), Call("P", poly, x))), e);
        return Disp(ForAll([B("f", new Formula.TypeArrow(Real, Real)), B("B", Real), B("e", Real)],
            Imp(All(Call("ContDiff", Real, Infty, f), Lt(D(0), r), Lt(D(0), e)),
                Some([B("p", RatPoly)], ForAll([B("x", Interval(r))], All(
                    BoundJet(f, p), BoundJet(df, dp), BoundJet(Call("D", df), Call("derivative", dp))))))));
    }

    private static Formula EvenPolynomial()
    {
        Formula p = F.Id("p"), q = F.Id("q"), x = F.Id("x");
        return Disp(ForAll([B("p", RatPoly), B("q", RatPoly), B("x", Real)],
            Eq(Call("rationalEvenPolynomial", p, q, x),
                Add(Call("S", p, x), Mul(F.Id("I"), Call("S", q, x))))));
    }

    private static Formula Cutoff()
    {
        Formula r = F.Id("R"), p = F.Id("p"), q = F.Id("q"), x = F.Id("x");
        return Disp(ForAll([B("R", Natural), B("p", RatPoly), B("q", RatPoly), B("x", Real)],
            Imp(Lt(D(0), r), Eq(At(Call("H", r, p, q), x),
                Mul(Call("chi", r, x), Call("rationalEvenPolynomial", p, q, x))))));
    }

    private static Formula Approximation(bool spectral)
    {
        Formula z = F.Id("Z"), g = F.Id("g"), r = F.Id("R"), e = F.Id("e");
        Formula p = F.Id("p"), q = F.Id("q"), h = Call("H", r, p, q);
        Formula physical = All(Support(h, Mul(D(2), r)), Lt(Call("J", Sub(g, h)), e));
        Formula result = spectral ? All(physical,
            Lt(new Formula.Norm(Sub(Call("W", z, g), Call("W", z, h))), e)) : physical;
        Formula.BoundVariable[] variables = spectral
            ? [B("Z", F.Id("ZeroData")), B("g", F.Id("WeilTestFunction")), B("R", Natural), B("e", Real)]
            : [B("g", F.Id("WeilTestFunction")), B("R", Natural), B("e", Real)];
        return Disp(ForAll(variables, Imp(All(Lt(D(0), r), Support(g, r), Lt(D(0), e)),
            Some([B("p", RatPoly), B("q", RatPoly)], result))));
    }
}
