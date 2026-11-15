using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class CouplingWassersteinTriangleRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/beatty2025couplingwasserstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For pure-state transport plans with the trace-distance ground metric, an order-one coupling distance in dimension three has a long side at least 96/625 and two short sides totaling at most 3/20.",
        H("An order-one coupling Wasserstein distance violates the triangle inequality"),
        Blocks(
            Node("UnitVector", "Unit amplitude vectors", UnitVectorFormula(),
                "A vector is a function from Fin n to the complex numbers, with the sum of squared coordinate moduli equal to one. normSq is Complex.normSq, so it is the real squared complex modulus. Vectors differing by a unit complex phase represent the same pure projector. The existing rankOneDensity sends v to the matrix with entries v i times the conjugate of v j. This is the unit-vector presentation of the pure states in Definition 8.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ground", "The trace distance between pure states", GroundFormula(),
                "Section V.2, equation (81), gives this square-root expression for half the trace norm of the difference of the two unit-vector projectors. The complex inner product is the sum of conjugate u i times v i. The formula uses the real nonnegative square root; it depends only on the projectors and includes arbitrary complex amplitudes.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Plan", "Countable pure-state transport plans", PlanFormula(),
                "Definition 8 and equations (11) and (12) require the two weighted projector sums to be the indicated marginals. The displayed triple contains a real weight sequence and two sequences of unit vectors. HasSum denotes convergence of the unordered finite partial sums, and the real scalar action multiplies every matrix entry by the real weight. The explicit mass equation HasSum q 1 follows from either density marginal by taking the trace, since each unit projector has trace one. It is retained as a redundant normalization field.\n" +
                "Natural-number indices with nonnegative weights represent the same plans as the source's countable index sets with strictly positive weights. Remove zero-weight terms in one direction; enumerate the positive terms and pad with zeros in the other. Both operations preserve the marginals and cost. Finite plans are included by zero padding. This correspondence is an explanation of the representation; no additional equivalence theorem is asserted.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cost", "The order-one cost", CostFormula(),
                "Definition 9, equation (15), specialized to order one. Every ground cost is nonnegative because the real square root is nonnegative, and is at most one because the squared complex modulus is nonnegative and Real.sqrt_le_one applies. Thus the nonnegative weighted cost is bounded termwise by the weight sequence, whose sum is one, so the real tsum is convergent and agrees with the ordinary plan cost. A zero-weight term contributes zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("wasserstein", "The coupling infimum", WassersteinFormula(),
                "Definition 9, equation (16), specialized to order one: the outer power 1/p is then one. The infimum is over all countable plans, with no restriction to a chosen finite family. The real sInf convention is total on arbitrary sets; the estimates in the counterexample use nonempty cost sets bounded below by zero, so they use the ordinary real infimum.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal order-one triangle assertion", ClaimFormula(),
                "The introduction states: “Although many desirable properties of these W_p^d are proven in Sec. IV, establishing a triangle inequality remains a difficult open problem.” Appendix C states: “the triangle inequality eludes us.” Here the triangle assertion ranges over every natural dimension and three arbitrary density matrices, meaning positive semidefinite matrices with trace one. The ground distance is exactly the trace-distance choice in equation (81), and the transport order is one. Pure and singular density matrices are included. The empty-dimensional case is retained literally; it supplies no trace-one states.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A three-dimensional counterexample", new Formula.Not(Call("claim")),
                "Use coordinates numbered zero, one and two. Put p=(4/5,3/5,0), q=(3/5,4/5,0), P=|p⟩⟨p|, Q=|q⟩⟨q|, R=(P+Q)/2 and s=1/100. Let E k be the kth coordinate projector, B=R−s E 0 and σ=B+s E 2. In the first two coordinates B has matrix [[49/100,12/25],[12/25,1/2]]. The unit vector u=(119/169,120/169,0) gives B=(28561/29750)|u⟩⟨u|+(7/500)E 0+(19/1190)E 1. These positive coefficients sum to 99/100. This decomposition also establishes positivity of B and σ.\n" +
                "The plan with weight 1/2 on (p,p) and 1/2 on (p,q) has marginals P and R and cost 7/50, since the ground distances are zero and 7/25. Match the three displayed components of B to themselves, then put weight s on (e 0,e 2). This plan has marginals R and σ and cost 1/100. Hence the two short sides total at most 3/20.\n" +
                "Consider an arbitrary countable plan with source P and denote its source vectors by ψ j. Apply the source marginal to the quadratic forms normSq(3 ψ j 0−4 ψ j 1) and normSq(ψ j 2). Their nonnegative weighted sums are both zero because p=(4/5,3/5,0). Hence each positive-weight source term satisfies 3 ψ j 0=4 ψ j 1 and ψ j 2=0. Unit normalization then forces its projector to equal P. Its ground cost to any target v therefore equals the ground cost from p to v; zero-weight terms contribute nothing.\n" +
                "For the pointwise estimate take a complex unit vector v, and locally write z=v 0, w=v 1, q=|z|²+|w|², t=|v 2|², r=|−3z/5+4w/5|² and L=−9|z|²/25+16|w|²/25. Unit normalization gives q+t=1, and the orthogonal change of coordinates gives 1−|⟨p,v⟩|²=r+t. The exact algebraic certificate q r−L²=((12/25)q−Re(z conj(w)))²+Im(z conj(w))² is nonnegative, so L≤sqrt(q r). Furthermore sqrt(r+t)≥sqrt(q r)+t: after squaring, the difference of the squared sides is t(r+q−2 sqrt(q r)), which is nonnegative by the arithmetic–geometric mean inequality. Thus the ground distance is at least L+t. Equivalently it is at least (7/50)q−(|z|²−|w|²)/2+t. These identities retain the imaginary part explicitly and apply to all complex amplitudes.\n" +
                "Summation against the target marginal replaces the three coordinate masses by 49/100, 1/2 and 1/100. Every plan from P to σ therefore has cost at least −(9/25)(49/100)+(16/25)(1/2)+1/100=96/625. An explicit plan from P to σ uses the four target components of σ with constant source p, so this cost set is nonempty. Its infimum is at least 96/625. Since 96/625>3/20, the long side strictly exceeds the sum of the two short sides. The counterexample and the estimates are the construction here; the plans and distances are from the cited definitions.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("beatty-stilck-franca-2024-coupling-wasserstein-triangle"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("bsfwone-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(prose.Split('\n').Select(part => Paragraph(Text(part))).ToArray()), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Typed(Formula x, Formula type) => Seq(x, Colon, Sp, type);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(x, type), Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(x, type), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Product(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula N => X("n");
    private static Formula FinN => Call("Fin", N);
    private static Formula Mat => Call("Matrix", FinN, FinN, Complexes);
    private static Formula Unit => Call("UnitVector", N);
    private static Formula SumOver(Formula x, Formula type, Formula value) =>
        Seq(new Formula.Subscript(Sum, Seq(x, InMacro, Sp, type)), Sp, value);
    private static Formula Lam(Formula x, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(x, type), Sp, Mapsto, Sp, Par(body));
    private static Formula Tsum(Formula body) => Call("tsum", Lam(X("j"), Naturals, body));
    private static Formula SetOf(Formula x, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(x, type), Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula ForStates(Formula body) => All(N, Naturals,
        All(Rho, Mat, All(SigmaLower, Mat, body)));
    private static Formula Proj(Formula v) => Call("rankOneDensity", v);
    private static Formula Plans => Call("Plan", Rho, SigmaLower);

    private static Formula UnitVectorFormula()
    {
        Formula v = X("v"), i = X("i");
        return All(N, Naturals, Eq(Unit, SetOf(v, Arrow(FinN, Complexes),
            Eq(SumOver(i, FinN, Call("normSq", At(v, i))), D(1)))));
    }

    private static Formula GroundFormula()
    {
        Formula u = X("u"), v = X("v"), i = X("i");
        Formula inner = SumOver(i, FinN, Mul(Call("conj", At(u, i)), At(v, i)));
        return All(N, Naturals, All(u, Unit, All(v, Unit,
            Eq(Call("ground", u, v), Call("sqrt", Sub(D(1), Call("normSq", inner)))))));
    }

    private static Formula PlanFormula()
    {
        Formula q = X("q"), u = X("u"), v = X("v"), j = X("j");
        Formula triple = Seq(Open, q, Comma, Sp, u, Comma, Sp, v, Close);
        Formula type = Product(Arrow(Naturals, Reals),
            Product(Arrow(Naturals, Unit), Arrow(Naturals, Unit)));
        Formula left = Call("HasSum", Lam(j, Naturals, Mul(At(q, j), Proj(At(u, j)))), Rho);
        Formula right = Call("HasSum", Lam(j, Naturals, Mul(At(q, j), Proj(At(v, j)))), SigmaLower);
        Formula conditions = And(All(j, Naturals, Le(D(0), At(q, j))),
            And(left, And(right, Call("HasSum", q, D(1)))));
        return ForStates(Eq(Plans, SetOf(triple, type, conditions)));
    }

    private static Formula CostFormula()
    {
        Formula p = X("Q"), j = X("j");
        Formula value = Tsum(Mul(At(Call("weight", p), j),
            Call("ground", At(Call("source", p), j), At(Call("target", p), j))));
        return ForStates(All(p, Plans, Eq(Call("cost", p), value)));
    }

    private static Formula WassersteinFormula()
    {
        Formula p = X("Q"), r = X("r");
        return ForStates(Eq(Call("wasserstein", Rho, SigmaLower), Call("sInf",
            SetOf(r, Reals, Some(p, Plans, Eq(r, Call("cost", p)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula t = X("T");
        Formula inequality = Le(Call("wasserstein", Rho, SigmaLower),
            Add(Call("wasserstein", Rho, t), Call("wasserstein", t, SigmaLower)));
        Formula assertion = All(N, Naturals, All(Rho, Mat, All(t, Mat, All(SigmaLower, Mat,
            Imp(Call("IsDensity", Rho), Imp(Call("IsDensity", t),
                Imp(Call("IsDensity", SigmaLower), inequality)))))));
        return IffOf(Call("claim"), assertion);
    }
}
