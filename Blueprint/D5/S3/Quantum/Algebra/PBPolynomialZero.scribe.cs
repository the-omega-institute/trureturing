using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBPolynomialZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the same original real Jordan carrier, the full PB identity and the explicit rotation, oddness and affine-zero rows imply zero response for every pair of polynomials in one generator.",
        H("All polynomial pairs under the original symmetry rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("polynomial-evaluation"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBPolynomialZero.eval"),
                H("Evaluation by the original Jordan powers"),
                StatementSource.FromAuthor(Disp(EvaluationStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("E is any real normed vector space, J is its specified real bilinear product, and u and x are specified original elements. The finite coefficient sum defines a real-linear evaluation map. The existing JBAlgebra.npow has zeroth power u and successor J(x,power). No algebra law is required for this definition. When JBAlgebra.Data holds, its existing power_mul theorem proves that this evaluation also preserves multiplication. All resulting labels remain in E."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("all-polynomial-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBPolynomialZero.polynomial_zero"),
                H("The full formal-degree induction"),
                StatementSource.FromAuthor(Disp(ZeroStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("JBAlgebra.Data(E,J,u) supplies symmetry, the unit law, the Jordan identity, product norm domination, the square norm identity and square norm monotonicity for this same J and norm. No completeness, nonzero-space, dimension, spectrum or representation condition is imposed. D is an arbitrary total map from E squared to E. The hypotheses on D are exactly the full PB identity and the SO(2) rotation, each-slot oddness and same-axis affine-zero rows of source 185.1. The square row and a separate unit row are unnecessary inputs. These rows are hypotheses here; their derivation from raw P2 and PB is not supplied by this theorem.")),
                    Paragraph(Text("For complex scalar polynomials P, take their coefficientwise real and imaginary parts h,k and put Phi(P)=D(eval(h),eval(k)). Complex coefficients record two real labels; D never receives a complex argument. The rotation hypothesis gives Phi(zP)=Phi(P) for every unit complex scalar z. Oddness gives Phi(-P)=Phi(P) and Phi(conjugate(P))=-Phi(P). Neither additivity nor arbitrary scalar homogeneity of D or Phi is inferred.")),
                    Paragraph(Text("Strong induction uses an arbitrary natural bound on the formal degree of P. Degrees at most one follow from the affine-zero row with generator eval(T), including the zero polynomial and all constants. Otherwise the complex fundamental theorem of algebra factors P as kappa times the product of T-z over the list of roots, with repeated roots retained at their multiplicities. The nonzero leading coefficient kappa is a scalar, independent of possible collapse under evaluation.")),
                    Paragraph(Text("To reflect one nonreal root z=r+it, set a=(T-r)/t and W=-it Q, where Q contains kappa and all the other root factors, including the already reflected prefix. The real and imaginary parts of W have strictly smaller formal degree; a has degree at most one. Applying the induction hypothesis to (a,Re(W)) and (a,Im(W)) pays the two actual inner responses D(A,B)=D(A,C)=0, where A=eval(a), B=eval(Re(W)) and C=eval(Im(W)).")),
                    Paragraph(Text("The same original PB now compares exactly D(B-J(A,C),C+J(A,B)) and D(B+J(A,C),C-J(A,B)). Its full right side is twice the difference between J(B,J(A,C)) and J(C,J(A,B)); evaluation multiplicativity and the associativity of scalar polynomial multiplication make this zero. The two outer pairs are exactly the real labels of (1+ia)W=(T-z)Q and (1-ia)W=-(T-conjugate(z))Q. Simultaneous negation removes the second sign, so reflecting this root preserves the actual response. No unexplained root-invariance premise is used.")),
                    Paragraph(Text("Real roots are unchanged. Induction along the finite root list therefore reflects every indexed factor and gives kappa times the coefficient-conjugate monic product. This equals kappa/conjugate(kappa) times conjugate(P). That scalar has norm one. Phase invariance and second-slot oddness give Phi(P)=-Phi(P), and real scalar cancellation forces zero. Only nonzero real t and nonzero complex conjugate(kappa) are divided by; no root or inverse is taken inside E.")),
                    Paragraph(Text("The theorem quantifies all formal degrees without a bound. Zero real or imaginary parts, repeated roots, real roots, an empty root list, scalar generators, noninjective evaluation and the zero algebra remain included. There is no additivity, homogeneity, continuity, measurability, covariance or completion extension assumption on D.")),
                    Paragraph(Text("For the original source 3.1, restrict the supplied JB laws on X through the original isometric Jordan inclusion i:E to X: symmetry, unit and Jordan equations descend by injectivity, and the three norm laws descend by isometry and preservation of J and u. Apply the displayed theorem to exactly that original E,J,u,D and PB. Density, completeness of X, the original cone and evaluation family, directed P2 and all zero, unequal and subnormalised masses are retained by this application and are not used to derive the symmetry rows here. Thus this supplies the all-degree induction conditional on 185.1. The general original-unit and raw 185.1 derivations remain required for the unconditional source 3.1 conclusion. No response on a quotient, C* replacement, finite-spectrum restriction or transport of D to X is introduced."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => Call(s, xs);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => Equal(a, b);
    private static Formula Plus(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Add(a, b);
    private static Formula Minus(Formula a, Formula b) => Subtract(a, b);
    private static Formula Sm(Formula a, Formula b) => C("smul", a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula E => V("E");
    private static Formula Poly => C("Polynomial", R);
    private static Formula App(Formula f, params Formula[] xs) => C("apply", new[] { f }.Concat(xs).ToArray());
    private static Formula Response(Formula a, Formula b) => App(V("D"), a, b);
    private static Formula Ev(Formula p) => C("eval", V("J"), V("u"), V("x"), p);
    private static Formula Carrier(Formula body) => All("E", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", E), CloseBracket,
        OpenBracket, C("NormedSpace", R, E), CloseBracket, body));
    private static Formula Product(Formula body) => All("J", C("Bilinear", R, E, E, E), All("u", E, body));
    private static Formula EvaluationStatement()
    {
        var k = V("k"); var p = V("p");
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, InMacro, Sp, C("support", p))),
            Grp(Sm(C("coeff", p, k), C("npow", V("J"), V("u"), V("x"), k))));
        return Carrier(Product(All("x", E, All("p", Poly, Eq(Ev(p), sum)))));
    }
    private static Formula ZeroStatement()
    {
        var a = V("a"); var b = V("b"); var theta = V("theta");
        var co = C("cos", theta); var si = C("sin", theta);
        var rot = All("a", E, All("b", E, All("theta", R,
            Eq(Response(Minus(Sm(co, a), Sm(si, b)), Plus(Sm(si, a), Sm(co, b))), Response(a, b)))));
        var left = All("a", E, All("b", E, Eq(Response(Negate(a), b), Negate(Response(a, b)))));
        var right = All("a", E, All("b", E, Eq(Response(a, Negate(b)), Negate(Response(a, b)))));
        var affine = All("a", E, All("s", R, All("t", R, All("r", R, All("v", R,
            Eq(Response(Plus(Sm(V("s"), V("u")), Sm(V("r"), a)),
                Plus(Sm(V("t"), V("u")), Sm(V("v"), a))), Num(0)))))));
        var conditions = new[] { C("Data", E, V("J"), V("u")), C("PB", V("J"), V("D")), rot, left, right, affine }.Aggregate(And);
        return Carrier(Product(All("D", C("Function", E, E, E),
            Imp(conditions, All("x", E, All("p", Poly, All("q", Poly,
                Eq(Response(Ev(V("p")), Ev(V("q"))), Num(0)))))))));
    }
}
