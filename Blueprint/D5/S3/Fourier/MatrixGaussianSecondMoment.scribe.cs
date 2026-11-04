using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianSecondMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic current weights have absolutely convergent Gaussian lattice sums. Their coordinate Fourier transform yields inverse-matrix second-moment inversion with the principal complex power and a positive metric correction.",
        H("MatrixGaussianSecondMoment"), Blocks(
            Entry("integral-fourier-second-moment", "integral_fourier_second_moment", "Quadratic-weight Fourier integration", FourierFormula(),
                "For every finite rank, real positive definite Gram matrix A, complex b with positive real part, and real vectors u, v and w, the Fourier transform of B_A(u,x) B_A(v,x) exp(-pi b Q_A(x)) equals the determinant and principal-power factor times [B_A(u,v)/(2 pi b) - (u dot w)(v dot w)/b squared] exp(-pi Q_(A inverse)(w)/b). Real frequency differentiation is justified by integrable Gaussian majorants.", DescribeRole.Theorem),
            Entry("moment-term", "momentTerm", "Integer-coordinate current weight", MomentFormula(),
                "The weights are bilinear pairings with the original Gram matrix. No integrality or unimodularity condition is imposed on that matrix.", DescribeRole.Definition),
            Entry("second-moment", "secondMoment", "Second-moment theta series", SumFormula(),
                "The series sums the two current weights over the full integer-coordinate lattice.", DescribeRole.Definition),
            Entry("second-moment-inversion", "second_moment_inversion", "Principal-branch second-moment inversion", InversionFormula(),
                "For positive imaginary part of tau, the inverted series is absolutely summable and has the displayed sum. The dual Gram matrix is A inverse and its polarization vectors are A u and A v. The metric correction has coefficient tau/(2 pi i). Rank zero and zero polarizations are included. This is an analytic lattice identity; it does not assert modular invariance of the same matrix or a conformal-field trace evaluation.", DescribeRole.Theorem),
            Paragraph(Text("Writing A as the real Gram matrix of a positive lattice and taking u and v to be coordinate unit vectors identifies the weights with the two lattice-current charges. On the dual side the transported polarizations give the literal coordinate product k_i k_j. The covariance is the original Gram entry A_ij. This correspondence supplies a matrix-moment ingredient for current identities; the operator trace, annular continuation and full modular current theorem require their own proofs.")),
            Paragraph(Text("The unweighted coordinate Fourier transform, Gaussian convergence, coordinate Poisson summation and theta principal-branch algebra are reused from MatrixGaussian, MatrixGaussianPoisson, CoordinatePoisson and MatrixGaussianTheta. The polynomial calculation is a synthesis of those suppliers with dominated differentiation; no claim of a new classical analytic identity is made.")))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("matrixgaussiansecondmoment-" + id),
            DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianSecondMoment." + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Imag => Seq(Operatorname,Grp(V("Complex")),Dot,Operatorname,Grp(V("I")));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula All(string s, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t,p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Pos(Formula a) => new Formula.Relation(D(0),FormulaRelationOperator.LessThan,a);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Inv(Formula a) => Pow(a,NegF(D(1)));
    private static Formula AddF(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula SubF(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Cast(Formula a) => Seq(Open,a,Colon,C,Close);
    private static Formula Lam(string s, Formula t, Formula p) => Seq(Open,V(s),Colon,t,Sp,Mapsto,Sp,p,Close);
    private static Formula At(Formula f, Formula x) => Seq(f,Open,x,Close);
    private static Formula FinR => Call("Fin",V("r"));
    private static Formula Vec => Arr(FinR,R);
    private static Formula Lattice => Arr(FinR,Z);
    private static Formula Mat => Call("Matrix",FinR,FinR,R);
    private static Formula Q(Formula a,Formula x) => Call("quadratic",a,x);
    private static Formula B(Formula a,Formula u,Formula x) => Call("dotProduct",u,Call("mulVec",a,x));
    private static Formula E(Formula x) => Call("exp",x);
    private static Formula IntVec(Formula a) => Lam("i",FinR,Seq(Open,At(a,V("i")),Colon,R,Close));
    private static Formula Term(Formula tau) => Call("momentTerm",V("A"),V("u"),V("v"),tau,V("n"));
    private static Formula Sum(string s,Formula t,Formula p) => Call("tsum",Lam(s,t,p));
    private static Formula Rank(Formula p) => All("r",N,All("A",Mat,p));
    private static Formula Polar(Formula p) => All("u",Vec,All("v",Vec,p));
    private static Formula Positive(Formula p) => Imp(Call("PosDef",V("A")),p);
    private static Formula Prefactor(Formula b) => Mul(Inv(Cast(Call("sqrt",Call("det",V("A"))))),Pow(b,Div(NegF(Cast(V("r"))),D(2))));

    private static Formula MomentFormula()
    {
        var weight = Mul(Cast(B(V("A"),V("u"),IntVec(V("n")))), Cast(B(V("A"),V("v"),IntVec(V("n")))));
        var exponent = Mul(Mul(Mul(Pi,Imag),V("tau")), Cast(Q(V("A"),IntVec(V("n")))));
        return Disp(Rank(Polar(All("tau",C,All("n",Lattice,Equal(Term(V("tau")),Mul(weight,E(exponent))))))));
    }
    private static Formula SumFormula() => Disp(Rank(Polar(All("tau",C,
        Equal(Call("secondMoment",V("A"),V("u"),V("v"),V("tau")), Sum("n",Lattice,Term(V("tau"))))))));
    private static Formula FourierFormula()
    {
        var phase = E(Mul(Mul(NegF(D(2)),Mul(Pi,Imag)),Cast(Call("dotProduct",V("w"),V("x")))));
        var gaussian = E(Mul(Mul(NegF(Pi),V("b")),Cast(Q(V("A"),V("x")))));
        var integrand = Mul(Mul(Mul(phase,Cast(B(V("A"),V("u"),V("x")))),Cast(B(V("A"),V("v"),V("x")))),gaussian);
        var covariance = Div(Cast(B(V("A"),V("u"),V("v"))),Mul(Mul(D(2),Pi),V("b")));
        var frequency = Div(Mul(Cast(Call("dotProduct",V("u"),V("w"))),Cast(Call("dotProduct",V("v"),V("w")))),Pow(V("b"),D(2)));
        var dualGaussian = E(Mul(Div(NegF(Pi),V("b")),Cast(Q(Inv(V("A")),V("w")))));
        var rhs = Mul(Mul(Prefactor(V("b")),SubF(covariance,frequency)),dualGaussian);
        return Disp(Rank(Positive(All("b",C,Imp(Pos(Call("re",V("b"))),Polar(All("w",Vec,
            Equal(Call("integral",Lam("x",Vec,integrand)),rhs))))))));
    }
    private static Formula InversionFormula()
    {
        var inverted = Div(NegF(D(1)),V("tau"));
        var convergence = Call("Summable",Lam("n",Lattice,new Formula.Norm(Term(inverted))));
        var prefactor = Div(Pow(Mul(NegF(Imag),V("tau")),Div(Cast(V("r")),D(2))),Cast(Call("sqrt",Call("det",V("A")))));
        var dualMoment = Call("secondMoment",Inv(V("A")),Call("mulVec",V("A"),V("u")),Call("mulVec",V("A"),V("v")),V("tau"));
        var correction = Mul(Mul(Div(V("tau"),Mul(Mul(D(2),Pi),Imag)),Cast(B(V("A"),V("u"),V("v")))),Call("theta",Inv(V("A")),V("tau")));
        var value = Mul(prefactor,AddF(Mul(Pow(V("tau"),D(2)),dualMoment),correction));
        return Disp(Rank(Positive(Polar(All("tau",C,Imp(Pos(Call("im",V("tau"))),
            AndF(convergence,Call("HasSum",Lam("n",Lattice,Term(inverted)),value))))))));
    }
}
