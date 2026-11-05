using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class JonesAloyEntropyConstancyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/JonesAloyEntropyConstancy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/jones2026speedlimits");
    private const string Quote = "Appendix E(ii), p. 16, after Lemma 3: “Indeed, we conjecture – and the numerics suggest – that H⋆ is constant on those lines, i.e. that we have equality in Lemma 3. However, we have not managed to prove this.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entropy minimum under an exact mean energy constraint is not constant on fixed-difference correlation lines.",
        H("Entropy constancy on quantum correlation lines fails"),
        Blocks(
            Node("gamma", "The minimum state overlap", GammaFormula(),
                "Equation (9), p. 4, defines the smallest possible overlap by the cosine below pi/2 and zero otherwise, in units with time separation and Planck's constant equal to one. Energy labels range over all nonnegative real numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fidelityExpression", "The correlation overlap expression", FidelityFormula(),
                "Equation (8), p. 4, gives one half of the sum of the two products of square roots. Each square root is taken separately.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("quantumSet", "The quantum correlation domain", QuantumFormula(),
                "Equations (7)–(9), p. 4, characterize the correlations by the overlap inequality inside the square [-1,1] squared. The displayed set uses that characterization.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("entropy", "The entropy of a correlation pair", EntropyFormula(),
                "Equation (27), p. 14: “Here we assume p(x)=1/2 for both x, i.e. there is equal a priori probability for both inputs.” The displayed expression uses CloningMachine.binaryEntropyBits at (1+C.1)/2 and (1+C.2)/2, including its endpoint values.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Ensemble", "Finite hidden-variable ensembles", EnsembleFormula(),
                "The source describes the ensemble {p(lambda),(C^lambda,E^lambda)}. An Ensemble n stores its real weights, correlation pairs and real energy labels at indices in Fin n. The optimization ranges over every natural number n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Feasible", "The exact optimization constraints", FeasibleFormula(),
                "Equation (27), p. 14, imposes the two correlation means, the exact mean energy and quantum-domain membership of every component. Probability weights are nonnegative and sum to one; energy labels are nonnegative without a componentwise upper bound.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("entropyValues", "The attainable entropy values", ValuesFormula(),
                "Equation (27), p. 14, minimizes the weighted sum of branch entropies over hidden-variable decompositions. This set collects those sums over every finite size, with all constraints retained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceRoof", "The attained-minimum specification", RoofFormula(),
                "The minimum in Equation (27), p. 14, is expressed by IsLeast on the attainable values, at every nonnegative energy and every correlation in its domain. It specifies attainment as well as the lower-bound property.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The line-constancy conjecture", Disp(IffTo(X("claim"), ClaimBody())),
                Quote + " The coordinates are the two real components of C. The center of its fixed-difference line is ((C.1-C.2)/2,-(C.1-C.2)/2). The statement includes existence of a function attaining every minimum, then asks every such function to have equal values at C and its center for energies in [0,pi/2].",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation of line constancy", Disp(Seq(Neg, Parenthesized(ClaimBody()))),
                "For every 24/25 <= s < 1 and every function HStar satisfying IsSourceRoof, its value at (s squared,-s squared) and energy Real.arcsin(s), plus 7((1-s)/2) squared, is strictly smaller than its value at (1,1-2s squared) at the same energy. An extremal first coordinate forces every positive-weight branch onto the boundary. A strict supporting tangent and the exact energy mean then force all these branches to have the same correlation. At the midpoint, the correlations (s,-s), (1,1) and (-1,-1) with weights s, (1-s)/2 and (1-s)/2 give a cheaper ensemble. Taking s=24/25 contradicts the displayed conjecture. Global existence of the minimum function, persistence into the interior and operator realizations are not proved here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("jahm-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Q(owner), Dot, Q(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula RCall(string name, params Formula[] args) => new Formula.Apply(Qualified("Real", name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Corr() => Seq(Real(), Times, Real());
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Fst(Formula c) => Seq(c, Dot, D(1));
    private static Formula Snd(Formula c) => Seq(c, Dot, D(2));
    private static Formula Field(Formula a, string field, Formula i) => App(Seq(a, Dot, Q(field)), i);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula MinusOf(Formula a) => new Formula.Negate(Parenthesized(a));
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula SumFin(Formula n, Formula body) => Seq(Sum, Underscore, Grp(Seq(X("i"), Colon, Call("Fin", n))), Sp, Parenthesized(body));
    private static Formula Bits(Formula p) => App(Seq(Q("D5"), Dot, Q("S3"), Dot, Q("Quantum"), Dot, Q("CloningMachine"), Dot, Q("binaryEntropyBits")), p);
    private static Formula RoofType() => Arrow(Parenthesized(Corr()), Arrow(Real(), Real()));

    private static Formula GammaFormula()
    {
        var e = X("e");
        return Disp(All("e", Real(), EqTo(Call("gamma", e),
            Seq(Q("if"), Sp, Parenthesized(LtTo(e, Div(Qualified("Real", "pi"), D(2)))), Sp,
                Q("then"), Sp, RCall("cos", e), Sp, Q("else"), Sp, D(0)))));
    }

    private static Formula FidelityFormula()
    {
        var c = X("C");
        return Disp(All("C", Corr(), EqTo(Call("fidelityExpression", c), Div(Add(
            Mul(RCall("sqrt", Add(D(1), Fst(c))), RCall("sqrt", Add(D(1), Snd(c)))),
            Mul(RCall("sqrt", Sub(D(1), Fst(c))), RCall("sqrt", Sub(D(1), Snd(c))))), D(2)))));
    }

    private static Formula QuantumFormula()
    {
        var c = X("C"); var e = X("e");
        var body = And(LeTo(MinusOf(D(1)), Fst(c)), And(LeTo(Fst(c), D(1)),
            And(LeTo(MinusOf(D(1)), Snd(c)), And(LeTo(Snd(c), D(1)),
                LeTo(Call("gamma", e), Call("fidelityExpression", c))))));
        return Disp(All("e", Real(), EqTo(Call("quantumSet", e),
            Seq(OpenBrace, X("C"), Colon, Corr(), Sp, Bar, Sp, body, CloseBrace))));
    }

    private static Formula EntropyFormula()
    {
        var c = X("C");
        return Disp(All("C", Corr(), EqTo(Call("entropy", c),
            Div(Add(Bits(Div(Add(D(1), Fst(c)), D(2))), Bits(Div(Add(D(1), Snd(c)), D(2)))), D(2)))));
    }

    private static Formula EnsembleFormula()
    {
        var n = X("n"); var a = X("A"); var fin = Call("Fin", n);
        return Disp(All("n", Nat(), All("A", Call("Ensemble", n), Seq(
            a, Dot, Q("weight"), Colon, Arrow(fin, Real()), Semi, Sp,
            a, Dot, Q("corr"), Colon, Arrow(fin, Parenthesized(Corr())), Semi, Sp,
            a, Dot, Q("energy"), Colon, Arrow(fin, Real())))));
    }

    private static Formula FeasibleFormula()
    {
        var n = X("n"); var a = X("A"); var c = X("C"); var e = X("E"); var i = X("i");
        var w = Field(a, "weight", i); var ci = Field(a, "corr", i); var ei = Field(a, "energy", i);
        var body = And(All("i", Call("Fin", n), LeTo(D(0), w)),
            And(EqTo(SumFin(n, w), D(1)), And(All("i", Call("Fin", n), LeTo(D(0), ei)),
            And(All("i", Call("Fin", n), Mem(ci, Call("quantumSet", ei))),
            And(EqTo(SumFin(n, Mul(w, Fst(Parenthesized(ci)))), Fst(c)),
            And(EqTo(SumFin(n, Mul(w, Snd(Parenthesized(ci)))), Snd(c)),
                EqTo(SumFin(n, Mul(w, ei)), e)))))));
        return Disp(All("n", Nat(), All("A", Call("Ensemble", n), All("C", Corr(), All("E", Real(),
            IffTo(Call("Feasible", a, c, e), body))))));
    }

    private static Formula ValuesFormula()
    {
        var n = X("n"); var a = X("A"); var c = X("C"); var e = X("E"); var i = X("i");
        var body = Ex("n", Nat(), Ex("A", Call("Ensemble", n),
            And(Call("Feasible", a, c, e), EqTo(X("z"), SumFin(n,
                Mul(Field(a, "weight", i), Call("entropy", Field(a, "corr", i))))))));
        return Disp(All("C", Corr(), All("E", Real(), EqTo(Call("entropyValues", c, e),
            Seq(OpenBrace, X("z"), Colon, Real(), Sp, Bar, Sp, body, CloseBrace)))));
    }

    private static Formula RoofFormula()
    {
        var h = X("HStar"); var e = X("E"); var c = X("C");
        return Disp(All("HStar", RoofType(), IffTo(Call("IsSourceRoof", h),
            All("E", Real(), Imp(LeTo(D(0), e), All("C", Corr(),
                Imp(Mem(c, Call("quantumSet", e)), Call("IsLeast", Call("entropyValues", c, e), App(h, c, e)))))))));
    }

    private static Formula ClaimBody()
    {
        var h = X("HStar"); var e = X("E"); var c = X("C");
        var center = Pair(Div(Sub(Fst(c), Snd(c)), D(2)), Div(MinusOf(Sub(Fst(c), Snd(c))), D(2)));
        var equality = EqTo(App(h, c, e), App(h, center, e));
        var correlations = All("C", Corr(), Imp(Mem(c, Call("quantumSet", e)), equality));
        var energies = All("E", Real(), Imp(LeTo(D(0), e),
            Imp(LeTo(e, Div(Qualified("Real", "pi"), D(2))), correlations)));
        return And(Ex("HStar", RoofType(), Call("IsSourceRoof", h)),
            All("HStar", RoofType(), Imp(Call("IsSourceRoof", h), energies)));
    }
}
