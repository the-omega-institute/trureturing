using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class FourierWindowFiniteRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-measure Fourier windows admit one shared ordered-monomial finite-rank approximation with explicit factorial operator-norm error.",
        H("Finite Fourier Window Approximation"),
        Blocks(Describe.Lean(
            DescribeId.Create("fourier-window-finite-rank-approximation"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/FourierWindowFiniteRank.fourier_window_finite_rank_approximation"),
            H("Shared witnesses for the actual two-window Fourier operator"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The telescope ranges over every natural number n, measurable subsets A and B of E = EuclideanSpace Real (Fin n), and nonnegative real bounds a and b. The measure mu is actual Lebesgue volume, H is complex Lp at exponent two, and the local Fact instance is 1 <= 2 in ENNReal. The eight hypotheses are nonnegativity of a and b, measurability of A and B, their ENNReal measures unequal to infinity, and the pointwise norm bounds on every point of the corresponding window. RealVolume(S) means mu.real S.")),
                Paragraph(Text("M(S,hS,hmuS) is the actual continuous linear multiplier given by holderL of indicatorConstLp at exponent infinity with scalar one. MA = M(A,hA,hmuA), MB = M(B,hB,hmuB), F is Lp.fourierTransform linear isometry viewed as a continuous linear map, and T = MB composed with F composed with MA. No integral representation, operator estimate, finite rank or compactness is assumed.")),
                Paragraph(Text("q = -2*pi*i, phase(x,xi) = q times the real inner product of x and xi cast to Complex, P(N,x,xi) = sum over k < N of phase(x,xi)^k / k!, and R = 2*pi*a*b. Tuple(k,n) is the full ordered coordinate type Fin k -> Fin n. mon(k,s,x) is the product over j : Fin k of x(s(j)), cast from Real to Complex. coeff(k) = q^k / k!. All products include the empty product at k = 0.")),
                Paragraph(Text("vin and vout are dependent families indexed by every k and every s : Tuple(k,n), taking values in the same actual H. VinWindow is the mu-almost-everywhere equality of the representative of vin(k,s) with A.indicator(mon(k,s)). VoutWindow is the corresponding equality with xi mapping to coeff(k) times B.indicator(mon(k,s))(xi). VinPairing is inner Complex (vin(k,s)) f = integral over A of mon(k,s,x)*f(x) with respect to mu, for every f : H. The inner product is conjugate linear in its first slot; mon is real-valued.")),
                Paragraph(Text("I(N) = Sigma k : Fin N, (Fin k -> Fin n). For these same existential families, TN(N) is the sum over i : I(N) of rankOne Complex (vout(i.1,i.2)) (vin(i.1,i.2)), with output vector first and input vector second. InputSpan(N) and OutputSpan(N) are the complex spans of these finite indexed families, and OperatorRange(N) is the range of the underlying linear map of TN(N).")),
                Paragraph(Text("ActualKernel(T,f) states that the representative of T(f) is mu-almost-everywhere equal to B.indicator(xi mapping to the integral over A of exp(phase(x,xi))*f(x)). TaylorKernel(TN,N,f) states the same representative equality with P(N,x,xi) in the integrand. FiniteDimensional means finite dimension over Complex. Compact means IsCompactOperator, OperatorNorm is the continuous linear map norm, Ratio(N) = R / (N+1) with the natural denominator cast to Real, ErrorBound(N) = sqrt(mu.real A * mu.real B) * (2*R^N / N!), and Tendsto(TN,atTop,nhds(T)) is convergence in the operator-norm topology.")),
                Paragraph(Text("The conclusion retains both window representatives, every input pairing, both actual kernel formulas, both finite input/output spans, finite-dimensional operator range, compactness of every TN, TN(0)=0, the conditional factorial error estimate, the eventual ratio condition, norm convergence, compactness of T, and both degeneracy statements. If either window has zero measure, T and all TN vanish. If N is nonzero and n=0 or a=0 or b=0, T=TN(N). No positive dimension, positive volume, positive radius, or nonempty windows are imposed. In dimension zero the actual volume is Dirac volume; the empty tuple contributes the constant monomial one, so dimension zero does not imply T=0.")),
                Paragraph(Text("Schwartz test pairing identifies the native L2 Fourier transform with the integral of an integrable window representative. Expanding the coordinate inner product into ordered monomials gives the actual Taylor rank-one operator identity for the shared witnesses. An input-window Cauchy-Schwarz estimate and output-window L2 domination give the two-window operator norm estimate for the actual residual kernel. The existing exponential remainder estimate then gives the stated error. Finite-rank compactness, factorial decay and norm-closed compactness supply the limit conclusions.")),
                Paragraph(Text("The construction and residual operator estimate form one general theorem. Scalar exponential bounds, coordinate normalization, finite-dimensional APIs and compactness of norm limits reuse existing analysis; this presentation makes no claim of literature originality. It supplies the finite-window approximation subclause of the broader symplectic completion problem. Arbitrary-state tightness, first position/momentum domains, covariance, metaplectic implementation, normality and thermal clauses require additional results."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), setA = F.Id("A"), setB = F.Id("B");
        Formula vin = F.Id("vin"), vout = F.Id("vout"), k = F.Id("k"), s = F.Id("s"), f = F.Id("f"), index = F.Id("N");
        Formula natural = Seq(Mathbb, Grp(F.Id("N"))), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("E", n), hilbert = Call("L2", space, F.Id("volume"));
        Formula op = F.Id("T"), approx = Call("TN", index), zero = D(0);
        Formula hypotheses = And(
            Call("Nonnegative", a), Call("Nonnegative", b),
            Call("MeasurableSet", setA), Call("MeasurableSet", setB),
            Call("FiniteENNRealVolume", setA), Call("FiniteENNRealVolume", setB),
            All([Bound("x", setA)], Call("NormLe", F.Id("x"), a)),
            All([Bound("xi", setB)], Call("NormLe", F.Id("xi"), b)));
        Formula witnesses = And(
            All([Bound("k", natural), Bound("s", Call("Tuple", k, n))], Call("VinWindow", vin, k, s)),
            All([Bound("k", natural), Bound("s", Call("Tuple", k, n))], Call("VoutWindow", vout, k, s)),
            All([Bound("k", natural), Bound("s", Call("Tuple", k, n)), Bound("f", hilbert)], Call("VinPairing", vin, k, s, f)),
            All([Bound("f", hilbert)], Call("ActualKernel", op, f)),
            All([Bound("N", natural), Bound("f", hilbert)], Call("TaylorKernel", F.Id("TN"), index, f)),
            All([Bound("N", natural)], Call("FiniteDimensional", Call("InputSpan", index))),
            All([Bound("N", natural)], Call("FiniteDimensional", Call("OutputSpan", index))),
            All([Bound("N", natural)], Call("FiniteDimensional", Call("OperatorRange", index))),
            All([Bound("N", natural)], Call("Compact", approx)),
            Equal(Call("TN", zero), zero),
            All([Bound("N", natural)], Implies(
                Call("Le", Call("Ratio", index), new Formula.Fraction(D(1), D(2))),
                Call("Le", Call("OperatorNorm", Seq(op, Minus, approx)), Call("ErrorBound", index)))),
            Call("EventuallyAtTop", Seq(index, Mapsto, Call("Le", Call("Ratio", index), new Formula.Fraction(D(1), D(2))))),
            Call("Tendsto", F.Id("TN"), F.Id("atTop"), Call("nhds", op)),
            Call("Compact", op),
            Implies(Or(Equal(Call("Volume", setA), zero), Equal(Call("Volume", setB), zero)),
                And(Equal(op, zero), All([Bound("N", natural)], Equal(approx, zero)))),
            All([Bound("N", natural)], Implies(Call("Nonzero", index), Implies(
                Or(Equal(n, zero), Or(Equal(a, zero), Equal(b, zero))), Equal(op, approx)))));
        Formula family = Call("MonomialFamily", n, hilbert);
        return All([Bound("n", natural), Bound("A", Call("Set", space)), Bound("B", Call("Set", space)),
                    Bound("a", real), Bound("b", real)],
            Implies(hypotheses, new Formula.BindMany(FormulaQuantifier.Exists,
                [Bound("vin", family), Bound("vout", family)], witnesses)));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
}
