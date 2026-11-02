using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianSourcePoissonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix Gaussians with independent complex coordinate sources have normal lattice convergence and a sourceful Poisson formula in coordinate volume.",
        H("MatrixGaussianSourcePoisson"), Blocks(
            Entry("sourceGaussianMap", "Gaussian with independent complex sources", MapFormula(),
                "For any finite rank r, real Gram matrix A, complex b and complex coordinate vector z, this is the continuous real-coordinate function exp(-pi b Q_A(x)+sum_i z_i x_i).", DescribeRole.Definition),
            Entry("source_gaussian_bound", "Uniform source absorption", BoundFormula(false),
                "Assume Re b>0 and t>0 with t sum_i x_i squared bounded by Q_A(x) for every real x. If every real part of z_i has absolute value at most R, then the norm is bounded by exp(r R squared/(2 pi Re(b) t)) times the zero-source Gaussian with parameter b/2. The bound holds at every real point and includes rank zero.", DescribeRole.Theorem),
            Entry("polynomial_source_gaussian_bound", "Uniform absorption of every finite polynomial order", BoundFormula(true),
                "For every natural k, the additional coordinate sup-norm weight norm(x)^k is absorbed by k! exp(r (R+1) squared/(2 pi Re(b) t)) times the same Gaussian with parameter b/2. The proof uses the exponential-series factorial bound and a real sign shift in each source coordinate. No source summability or derivative-extraction hypothesis is assumed.", DescribeRole.Theorem),
            Entry("summable_norm_source_gaussian", "Absolute sourceful lattice convergence", SummableFormula(),
                "Positive definiteness supplies the lower bound t; the resulting half-parameter Gaussian is genuinely summable on every integer vector, including the zero-dimensional lattice.", DescribeRole.Theorem),
            Entry("locally_summable_norm_source_gaussian", "Normal convergence of integer periodizations", LocalFormula(),
                "For a fixed independent complex source, the compact sup norms of all integer translates are summable. This is the actual normal-convergence hypothesis consumed by CoordinatePoisson.tsum_eq_tsum_integral.", DescribeRole.Theorem),
            Entry("latticeSourceMap", "Lattice summand as a source function", LatticeFormula(false),
                "Each integer-vector summand is a continuous function on the whole complex source space.", DescribeRole.Definition),
            Entry("weightedLatticeSourceMap", "Polynomially weighted source function", LatticeFormula(true),
                "The weight is the kth power of the sup norm of the real integer coordinate vector.", DescribeRole.Definition),
            Entry("locally_summable_norm_polynomial_source", "Compact-uniform convergence for all fixed polynomial degrees", PolynomialLocalFormula(),
                "For every natural k and every compact subset of the full complex source space, the sup norms of the weighted lattice summands are summable. This supplies polynomial Gaussian majorants. A theorem exchanging arbitrary finite source derivatives with the sum is a separate obligation.", DescribeRole.Theorem),
            Entry("integral_fourier_source_gaussian", "The inverse-Gram Fourier Gaussian with source", FourierFormula(),
                "The Fourier transform equals the determinant and principal-power factor, times exp(Q_(A inverse)(z)/(4 pi b)), times the inverse-Gram Gaussian at b inverse with source -i A inverse z/b. The source square is bilinear, without conjugation.", DescribeRole.Theorem),
            Entry("poisson_gaussian_source", "Sourceful positive-matrix Poisson summation", PoissonFormula(),
                "The proof reuses the actual coordinate Fourier periodization engine. Positive definiteness proves the input integrability, the compact normal convergence and dual lattice summability. The conclusion has no Poisson, covariance or convergence certificate as a hypothesis.", DescribeRole.Theorem),
            Paragraph(Text("This general analytic supplier does not by itself identify the original mod-two charge cosets, their integral-unimodular dual reindexing, or the original fourierSign multiplier. It does not assert the original coset S/T laws, fullK, Jacobi, a VOA/CFT construction, BRST/string or AdS/CFT. The overarching original goal remains active.")))));

    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("matrixgaussiansourcepoisson-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianSourcePoisson."+name),H(title),
            StatementSource.FromAuthor(formula),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb,Grp(V("R")));
    private static Formula C => Seq(Mathbb,Grp(V("C")));
    private static Formula RV => new Formula.TypeArrow(Call("Fin",V("r")),R);
    private static Formula CV => new Formula.TypeArrow(Call("Fin",V("r")),C);
    private static Formula IV => new Formula.TypeArrow(Call("Fin",V("r")),V("Z"));
    private static Formula All(string s, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Pos(Formula x) => new Formula.Relation(D(0),FormulaRelationOperator.LessThan,x);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Inv(Formula a) => Pow(a,Neg(D(1)));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Cast(Formula a) => Seq(Open,a,Colon,C,Close);
    private static Formula Lam(string s, Formula t, Formula p) => Seq(Open,V(s),Colon,t,Sp,Mapsto,Sp,p,Close);
    private static Formula Sum(string s, Formula t, Formula p) => Call("tsum",Lam(s,t,p));
    private static Formula G(Formula a, Formula b, Formula z, Formula x) => Call("sourceGaussianMap",a,b,z,x);
    private static Formula ZG(Formula b, Formula x) => Call("gaussianMap",V("A"),b,x);
    private static Formula HalfB => Div(V("b"),D(2));
    private static Formula RealInt(Formula a) => Call("castRealVector",a);
    private static Formula Core(Formula p) => All("r",V("N"),All("A",Call("Matrix",Call("Fin",V("r")),Call("Fin",V("r")),R),All("b",C,p)));
    private static Formula Analytic(Formula p) => Core(Imp(Call("PosDef",V("A")),Imp(Pos(Call("re",V("b"))),All("z",CV,p))));
    private static Formula Factor => Mul(Mul(Inv(Cast(Call("sqrt",Call("det",V("A"))))),Pow(V("b"),Div(Neg(Cast(V("r"))),D(2)))),Call("exp",Div(Call("complexQuadratic",Inv(V("A")),V("z")),Mul(Mul(D(4),Pi),V("b")))));
    private static Formula DualSource => Div(Mul(Neg(V("i")),Call("mulVec",Call("mapOfReal",Inv(V("A"))),V("z"))),V("b"));
    private static Formula MapFormula()
    {
        var quadratic = Mul(Mul(Neg(Pi),V("b")),Cast(Call("quadratic",V("A"),V("x"))));
        var linear = Call("dotProduct",V("z"),Call("castComplexVector",V("x")));
        var rhs = Call("exp",Add(quadratic,linear));
        return Disp(Core(All("z",CV,All("x",RV,Equal(G(V("A"),V("b"),V("z"),V("x")),rhs)))));
    }
    private static Formula BoundFormula(bool polynomial)
    {
        var exponent = Div(Mul(V("r"),Pow(polynomial?Add(V("R"),D(1)):V("R"),D(2))),Mul(Mul(D(2),Mul(Mul(Pi,Call("re",V("b"))),V("t"))),D(1)));
        var c = polynomial?Mul(Call("factorial",V("k")),Call("exp",exponent)):Call("exp",exponent);
        var lhs = polynomial?Mul(Pow(Norm(V("x")),V("k")),Norm(G(V("A"),V("b"),V("z"),V("x")))):Norm(G(V("A"),V("b"),V("z"),V("x")));
        Formula result = All("x",RV,Le(lhs,Mul(c,Norm(ZG(HalfB,V("x"))))));
        if(polynomial) result=All("k",V("N"),result);
        return Disp(Core(Imp(Pos(Call("re",V("b"))),All("t",R,Imp(Pos(V("t")),Imp(Call("quadraticLowerBound",V("A"),V("t")),All("R",R,All("z",CV,Imp(Call("realSourceBound",V("z"),V("R")),result)))))))));
    }
    private static Formula SummableFormula() => Disp(Analytic(Call("Summable",Lam("a",IV,Norm(G(V("A"),V("b"),V("z"),RealInt(V("a"))))))));
    private static Formula LocalFormula() => Disp(Analytic(All("K",Call("Compacts",RV),Call("Summable",Lam("a",IV,Norm(Call("restrict",Call("translate",Call("sourceGaussianMap",V("A"),V("b"),V("z")),RealInt(V("a"))),V("K"))))))));
    private static Formula LatticeFormula(bool weighted)
    {
        var lhs=Call(weighted?"weightedLatticeSourceMap":"latticeSourceMap",weighted?new[]{V("A"),V("b"),V("k"),V("a"),V("z")}:new[]{V("A"),V("b"),V("a"),V("z")});
        var rhs=G(V("A"),V("b"),V("z"),RealInt(V("a")));
        if(weighted) rhs=Mul(Cast(Pow(Norm(RealInt(V("a"))),V("k"))),rhs);
        Formula result=All("a",IV,All("z",CV,Equal(lhs,rhs)));
        if(weighted) result=All("k",V("N"),result);
        return Disp(Core(result));
    }
    private static Formula PolynomialLocalFormula() => Disp(Core(Imp(Call("PosDef",V("A")),Imp(Pos(Call("re",V("b"))),All("k",V("N"),All("K",Call("Compacts",CV),Call("Summable",Lam("a",IV,Norm(Call("restrict",Call("weightedLatticeSourceMap",V("A"),V("b"),V("k"),V("a")),V("K")))))))))));
    private static Formula FourierFormula()
    {
        var phase=Call("exp",Mul(Mul(Mul(Neg(D(2)),Pi),V("i")),Cast(Call("dotProduct",V("w"),V("x")))));
        var lhs=Call("integral",Lam("x",RV,Mul(phase,G(V("A"),V("b"),V("z"),V("x")))));
        return Disp(Analytic(All("w",RV,Equal(lhs,Mul(Factor,G(Inv(V("A")),Inv(V("b")),DualSource,V("w")))))));
    }
    private static Formula PoissonFormula() => Disp(Analytic(Equal(Sum("a",IV,G(V("A"),V("b"),V("z"),RealInt(V("a")))),Mul(Factor,Sum("k",IV,G(Inv(V("A")),Inv(V("b")),DualSource,RealInt(V("k"))))))));
}
