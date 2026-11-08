using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class LagTwoOptimalBracketDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original synchronous law gives a ratio-less-than-two bracket and linear small-noise order.",
        H("The lag-two optimal-constant bracket"),
        Blocks(
            Paragraph(Text("The graph class consists of all connected locally finite simple graphs on an arbitrary vertex type, finite or infinite, with a nonempty finite neighbour set at every vertex. The probability space is arbitrary. OriginalLaw requires a probability measure and measurability, mutual independence and the prescribed coordinateLaw marginals only for initial slots and strictly positive-time fresh, refresh and choice slots. Initial and fresh opinions are fair independent bits, refresh controls have parameter epsilon, and each choice is uniform on its actual neighbour set. No condition is imposed on auxiliary slots at time zero. X is the original synchronous recursion; W(x,u,2,t) sums the equalities X(i,u)=X(i+2,u) for i from one through t.")),
            Describe.Lean(DescribeId.Create("voter-lag-two-constant"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.cOpt"),
                H("The full variance-value infimum"), StatementSource.FromAuthor(ConstantFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter")),
                Blocks(Paragraph(Text("Values(epsilon) consists exactly of Var(W(x,u,2,t);P)/t, quantified over arbitrary vertex and sample types, the graph class above, every measurable probability-space realization of OriginalLaw, every vertex u and every natural t at least one. Its definition retains the original P and coordinate assignment. A unit-interval parameter e with real value epsilon carries the marginal laws; it introduces no additional restriction on zero<epsilon<one. Outside the unit interval this class is empty; all bounds concern the stated open interval. The infimum does not assert attainment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("voter-lag-two-bracket"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.result"),
                H("The complete bracket and native two-vertex law"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter")),
                Blocks(Paragraph(Text("Here q(epsilon)=1-epsilon, p(epsilon)=(1+q(epsilon)^2)/2 and normalizedCopt(e)=copt(e)/e. ThetaRightZero means two-sided Big-O on the real right-neighbourhood filter at zero; liminfRightZero and limsupRightZero use exactly that filter. The displayed inequalities include the bracket, exact endpoint ratio, both expanded endpoint polynomials, the uniform epsilon/4 and epsilon bounds, and all three lower/upper-limit comparisons.")),
                    Paragraph(Text("Ktwo is the complete simple graph on Bool. For any original realization on this graph, bits(x,u,n+1) is the actual centre history Z(0),...,Z(n+1), where Z(k)=X(k,u). History(x,u,n,z) is its equality event with the specified binary string z, and HistoryNext additionally requires Z(n+2)=b. Entry(z,n) is the bit two time steps before that next bit. The ratio of the two real probabilities is the conditional probability on each positive-probability history. Indicate is one when its proposition holds and zero otherwise.")),
                    Paragraph(Text("For each natural N, Y(x,u,N) is the actual vector (Z(0),Z(1),E(2),...,E(N+1)), with E(k) indicating Z(k)=Z(k-2). ProductLaw(epsilon,N) is the product of independent Bernoulli laws, fair at indices zero and one and with parameter p(epsilon) at every later index. Thus N=0 gives independent fair Z(0),Z(1), and N=M-1 gives the full joint law through every horizon M at least two, including independence of all agreement bits from both initial bits. These variables are read from the original recursion on P. CastBinomial(t,p) is the pushforward of the natural-valued Binomial(t,p) law by the real cast.")),
                    Paragraph(Text("The variance and Binomial assertions use the actual W: its i-th summand is E(i+2), so the selected agreement coordinates are E(3),...,E(t+2). Every natural t is included. At t=0 the empty sum has the point-mass-at-zero Binomial law and zero variance."))), DescribeRole.Theorem),
            Paragraph(Text("The lower endpoint applies original_potential_path_bounds with lag two to each member of Values. For the upper endpoint, on Ktwo each actual neighbour is the other endpoint. Expanding two synchronous updates gives Z(n+2)=F(n+2,u) if the centre refreshes, F(n+1,other) if only the intermediate leaf refreshes, and Z(n) otherwise. These four refresh/fresh coordinates lie outside the causal inputs of the entire preceding centre history. Their native independent laws give the conditional kernel (1-q^2)/2+q^2 Indicate(b=Z(n)). The initial pair uses I(u) and the independent block consisting of R(1,u), F(1,u), I(other), giving its fair product law. Induction on the horizon appends one independent Bernoulli agreement to the actual innovation vector. Selecting the coordinates used by W gives its Binomial law and variance t p(1-p)=t(1-q^4)/4.")),
            Paragraph(Text("The Ktwo law is the specialization of the star-centre transition in Benjamini, Helman Tov and Zhukovskii, Theorem 6.1 proof, Section 6, pages 28-29; the finite-horizon relation above is established directly from the synchronous coordinates. The existing lower bound and pinned product-measure, independence, Bernoulli and Binomial results supply the remaining probability interfaces. Factorization yields the exact ratio; polynomial expansion yields the endpoint formulas; division by positive epsilon gives the uniform order and right-sided limit bounds. No exact value of the infimum, attainment, minimizing graph, or existence of the normalized limit is asserted."))), []));

    private static Formula X(string s) => F.Id(s);
    private static Formula Named(string s) => Seq(Operatorname, Grp(X(s)));
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Named(s), [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(a, D(n));
    private static Formula Frac(Formula a, byte n) => new Formula.Fraction(a, D(n));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula E() => X("epsilon");
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Q() => Par(Seq(D(1), Minus, E()));
    private static Formula P() => Frac(Seq(D(1), Plus, Pow(Q(), 2)), 2);
    private static Formula Opt(Formula e) => C("copt", e);
    private static Formula Conjoin(params Formula[] fs)
    {
        var r = fs[^1];
        for (var i = fs.Length - 2; i >= 0; i--) r = And(fs[i], r);
        return r;
    }
    private static Formula ConstantFormula() => Disp(All("epsilon", Real(),
        Eqn(Opt(E()), C("inf", C("Values", E())))));
    private static Formula Scalars()
    {
        var lo = Seq(D(1), Minus, Pow(Q(), 2));
        var hi = Seq(D(1), Minus, Pow(Q(), 4));
        var ratio = Seq(D(1), Plus, Pow(Q(), 2));
        var lowerPoly = Seq(D(2), Times, Sp, E(), Minus, Pow(E(), 2));
        var upperPoly = Seq(D(4), Times, Sp, E(), Minus, D(6), Times, Sp, Pow(E(), 2),
            Plus, D(4), Times, Sp, Pow(E(), 3), Minus, Pow(E(), 4));
        return Conjoin(Le(Frac(lo, 4), Opt(E())), Le(Opt(E()), Frac(hi, 4)),
            Eqn(new Formula.Fraction(hi, lo), ratio), Lt(ratio, D(2)),
            Le(Frac(lowerPoly, 4), Opt(E())), Le(Opt(E()), Frac(upperPoly, 4)),
            Le(Frac(E(), 4), Opt(E())), Le(Opt(E()), E()));
    }
    private static Formula Asymptotics() => Conjoin(
        C("ThetaRightZero", Named("copt"), Named("identity")),
        Le(Frac(D(1), 2), C("liminfRightZero", Named("normalizedCopt"))),
        Le(C("liminfRightZero", Named("normalizedCopt")), C("limsupRightZero", Named("normalizedCopt"))),
        Le(C("limsupRightZero", Named("normalizedCopt")), D(1)));
    private static Formula Native()
    {
        var history = C("History", X("x"), X("u"), X("n"), X("z"));
        var next = C("HistoryNext", X("x"), X("u"), X("n"), X("z"), X("b"));
        var kernel = Seq(Frac(Seq(D(1), Minus, Pow(Q(), 2)), 2), Plus,
            Pow(Q(), 2), Times, Sp, C("Indicate", Eqn(X("b"), C("Entry", X("z"), X("n")))));
        var transition = All("n", Nat(), All("z", C("Bits", Seq(X("n"), Plus, D(2))),
            All("b", Named("Bool"), Imp(Lt(D(0), C("P", history)),
                Eqn(new Formula.Fraction(C("P", next), C("P", history)), kernel)))));
        var joint = All("N", Nat(), C("HasLaw", C("Y", X("x"), X("u"), X("N")),
            C("ProductLaw", E(), X("N")), X("P")));
        var w = C("W", X("x"), X("u"), D(2), X("t"));
        var statistic = All("t", Nat(), And(
            C("HasLaw", w, C("CastBinomial", X("t"), P()), X("P")),
            Eqn(C("Var", w, X("P")), Frac(Seq(X("t"), Times, Sp,
                Par(Seq(D(1), Minus, Pow(Q(), 4)))), 4))));
        return All("O", Named("Type"), All("m", C("MeasurableSpace", X("O")),
            All("P", C("Measure", X("O"), X("m")), All("x", C("Coordinates", Named("Ktwo"), X("O")),
            Imp(C("OriginalLaw", Named("Ktwo"), X("P"), E(), X("x")),
                All("u", Named("Bool"), Conjoin(transition, joint, statistic)))))));
    }
    private static Formula ResultFormula() => Disp(All("epsilon", Named("UnitInterval"),
        Imp(And(Lt(D(0), E()), Lt(E(), D(1))), Conjoin(Scalars(), Asymptotics(), Native()))));
}
