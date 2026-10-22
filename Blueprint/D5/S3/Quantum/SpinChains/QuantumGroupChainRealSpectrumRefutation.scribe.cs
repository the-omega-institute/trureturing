using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class QuantumGroupChainRealSpectrumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/bytsko2011nonhermitian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive-coupling quantum-group spin chain has a nonreal eigenvalue.",
        H("A counterexample to real spectra with positive couplings"),
        Blocks(
            Node("digit", "Tensor-basis digits", DigitFormula(),
                "The tensor basis is indexed by base-(n+1) words of length N, with the leftmost "
                + "digit first. Throughout, val(x) is the natural value of a finite index, and "
                + "fin(t,d) is the element of Fin(d) with value t; its bound is supplied by the "
                + "displayed domains. div and mod are natural-number division and remainder, "
                + "and subtraction between natural numbers is truncated. cast(A,B,t) denotes "
                + "the canonical coercion of t from A to B, including every real-to-complex "
                + "and natural-to-real coercion in the formulas.", AssessedProvenance.FromRepo()),
            Node("qnum", "Real q-numbers", QnumFormula(),
                "The q-number [t] is sin(γt)/sin(γ). Real division is total, so this definition "
                + "also has a value when sin(γ)=0. The spectral claim below restricts γ to the "
                + "nonzero admissible range.", AssessedProvenance.FromLiterature(Source)),
            Node("q", "The deformation parameter", QFormula(),
                "The parameter q=exp(iγ) lies on the unit circle; I denotes the imaginary unit. "
                + "The defining algebra relations are [E,F]=(K²−K⁻²)/(q−q⁻¹), KE=qEK and "
                + "KF=q⁻¹FK, as in Eq. (Uq).", AssessedProvenance.FromLiterature(Source)),
            Describe.Example(
                DescribeId.Create("bytsko-spectrum-gamma-zero"),
                H("A particular admissible angle"),
                Disp(GammaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At γ₀=arccos(4/5), cos(γ₀)=4/5 and sin(γ₀)=3/5, so q(γ₀)=(4+3i)/5. "
                    + "In particular, 0<γ₀<π/2.")))),
            Node("weight", "Weights in the finite basis", WeightFormula(),
                "The natural parameter n is twice the spin S. Basis index i has weight "
                + "val(i)−n/2, so the increasing index order runs from −S to S.",
                AssessedProvenance.FromRepo()),
            Node("E", "The raising operator", EFormula(),
                "In the basis of weights −S,−S+1,…,S, the matrix entry with row i and column j "
                + "raises the weight by one. Its coefficient is the square root in Eq. (EFK), "
                + "with n=2S. The square root is taken in the reals before its complex coercion.",
                AssessedProvenance.FromLiterature(Source)),
            Node("F", "The lowering operator", FFormula(),
                "This is the lowering operator of Eq. (EFK), in the same increasing-weight "
                + "basis. The subtraction n−val(j)+1 is performed in the naturals before "
                + "coercion to the reals.", AssessedProvenance.FromLiterature(Source)),
            Node("K", "The diagonal weight operator", KFormula(false),
                "The diagonal entry at i is exp(iγ(val(i)−n/2)), the action of K in Eq. (EFK). "
                + "diagonal(f) has entries f(i) on the diagonal and zero off the diagonal.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Kinv", "The inverse weight operator", KFormula(true),
                "The diagonal entries are exp(−iγ(val(i)−n/2)), giving the inverse of K.",
                AssessedProvenance.FromLiterature(Source)),
            Node("tensorCasimir", "The tensor Casimir", TensorCasimirFormula(),
                "Here tensor is the Kronecker product with multiplication of complex entries. "
                + "The four local expressions de, df, dk and dki are the represented coproducts "
                + "Δ(E), Δ(F), Δ(K) and Δ(K⁻¹). Thus the formula is (π⊗π)Δ(C), using the "
                + "coproduct of Eq. (DelEFK) and the Casimir C=(EF+FE)/2−"
                + "cos(γ)(K−K⁻¹)²/(4sin²(γ)) of Eq. (C). It follows the definitional left side "
                + "of Eq. (dC2). smul denotes scalar multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Node("casimirValue", "Casimir values on irreducible summands", CasimirValueFormula(),
                "On the spin-l irreducible summand the Casimir value is [l][l+1], as stated "
                + "after Eq. (C). The successor l+1 is a natural number before coercion.",
                AssessedProvenance.FromLiterature(Source)),
            Node("orderedProduct", "Products in increasing index order", OrderedProductFormula(),
                "The empty product is one. Each recursive step multiplies on the right by "
                + "the next factor, fixing an order even in a noncommutative monoid. Bracketed "
                + "typeclass assumptions in the displays are anonymous instance arguments.",
                AssessedProvenance.FromRepo()),
            Node("projector", "The Casimir spectral projector", ProjectorFormula(),
                "With n=2S, this is P^{S,s} from Eq. (PjC). The product runs through l=0,…,n "
                + "in increasing order, inserting the identity at l=s. Each other factor is "
                + "(C^{S,S}−[l][l+1]I)/([s−l][s+l+1]). The denominator factors are separately "
                + "coerced to the complexes before multiplication and inversion. In the "
                + "spectral claim all these denominators are nonzero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("siteOperator", "Embedding an adjacent two-site operator", SiteOperatorFormula(),
                "The operator P acts at the adjacent positions val(m) and val(m)+1, numbered "
                + "from zero. Its matrix entry vanishes unless all other tensor digits agree. "
                + "This is the adjacent-site embedding used before Eq. (Hal), expressed in the "
                + "base-(n+1) tensor basis.", AssessedProvenance.FromLiterature(Source)),
            Node("hamiltonian", "The open-chain Hamiltonian", HamiltonianFormula(),
                "Equation (Hal) sums the adjacent projectors with real couplings. The index "
                + "m in Fin(N−1) corresponds to the source's bond m+1. Each coupling is "
                + "coerced from the reals to the complexes before scalar multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Positive couplings and the proposed real spectrum", ClaimFormula(),
                "Conjecture 3 asserts a real spectrum for positive couplings when |γ|<π/(2S). "
                + "Here n=2S≥1, 0≤s≤n and N≥2. The nonzero angle and explicit nonvanishing "
                + "projector denominators make the formulas applicable. Every nonzero vector "
                + "v satisfying H v=z v is asserted to have Im(z)=0.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("bytsko-spectrum-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-site spin-one counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                ResultProse(),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("bytsko-spectrum-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultProse() => Blocks(
        Paragraph(Text(
            "Take S=s=1, hence n=2, N=4, γ=γ₀=arccos(4/5), q=(4+3i)/5 and "
            + "a=(1,1,1). These satisfy 0<2|γ|<π, and the two required denominator "
            + "products, for l=0 and l=2, are 8/5 and −112/125.")),
        Paragraph(Text(
            "Order the two-site basis lexicographically by weights −1,0,1. The matrix 14·P^{1,1} is "
            + "[[0,0,0,0,0,0,0,0,0], "
            + "[0,7+24i,0,−25,0,0,0,0,0], "
            + "[0,0,25,0,30i,0,−25,0,0], "
            + "[0,−25,0,7−24i,0,0,0,0,0], "
            + "[0,0,30i,0,−36,0,−30i,0,0], "
            + "[0,0,0,0,0,7+24i,0,−25,0], "
            + "[0,0,−25,0,−30i,0,25,0,0], "
            + "[0,0,0,0,0,−25,0,7−24i,0], "
            + "[0,0,0,0,0,0,0,0,0]].")),
        Paragraph(Text(
            "Index the four-site basis by x=27i₁+9i₂+3i₃+i₄, with iⱼ∈{0,1,2}. "
            + "Define the 81-by-2 matrix W by its nonzero rows, whose entries are ordered "
            + "as columns 0 and 1: "
            + "26:(0,4900); 44:(−5500−4125i,3080+8190i); "
            + "50:(5500−4125i,−7000+5250i); 62:(8800−6600i,−9828+3696i); "
            + "68:(7920+10560i,−10080−13440i); 70:(−5500+4125i,7000−5250i); "
            + "74:(−8800+6600i,6300−8400i); 76:(−2420−6435i,7000+5250i); "
            + "78:(0,−1372+4704i). All other rows vanish.")),
        Paragraph(Text(
            "Let A=[[-11/14,1],[-275/196,25/14]] and B=[[1,0],[0,0]]. "
            + "For the adjacent embeddings P₁₂,P₂₃,P₃₄ of P^{1,1}, direct matrix "
            + "multiplication gives (P₁₂+P₃₄)W=WA and P₂₃W=WB. Therefore HW=W(A+B). "
            + "Put z=1+i√(11/14)=1+i√(22/7)/2 and y=(1,z−1+11/14). "
            + "The identity z²−2z+25/14=0 gives (A+B)y=zy. Consequently H(Wy)=z(Wy). "
            + "The component at x=26 is 4900(z−1+11/14), whose imaginary part is positive; "
            + "hence Wy is nonzero. Since Im(z)=√(11/14)>0, this positive-coupling "
            + "chain refutes the universal real-spectrum assertion. The construction uses "
            + "the algebra and projectors of Bytsko's paper; it does not settle the restriction s=0.")));

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Types() => Named("Type");
    private static Formula Fin(Formula bound) => Call("Fin", bound);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Cast(Formula from, Formula to, Formula value) => Call("cast", from, to, value);
    private static Formula NR(Formula value) => Cast(Nat(), Real(), value);
    private static Formula RC(Formula value) => Cast(Real(), Complex(), value);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula FracOf(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negated(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula SqrtOf(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Ite(Formula condition, Formula yes, Formula no) =>
        Call("ite", Parenthesized(condition), yes, no);
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp,
            Parenthesized(Seq(variable, Sp, Colon, Sp, type)), Comma, Sp, body));
    private static Formula Let(string name, Formula value, Formula body) =>
        Parenthesized(Seq(Named("let"), Sp, V(name), Sp, Eq, Sp, value, Semi, Sp, body));
    private static Formula Product(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, F.Times, Sp, Parenthesized(right));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula TwoSite(Formula n, Formula scalar) =>
        Call("Matrix", Product(Fin(Add(n, D(1))), Fin(Add(n, D(1)))),
            Product(Fin(Add(n, D(1))), Fin(Add(n, D(1)))), scalar);
    private static Formula Chain(Formula n, Formula N) => Fin(Pow(Add(n, D(1)), N));
    private static Formula FinValue(Formula value, Formula bound) => Call("fin", value, bound);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Smul(Formula scalar, Formula value) => Call("smul", scalar, value);
    private static Formula Tensor(Formula left, Formula right) => Call("tensor", left, right);

    private static Formula DigitFormula()
    {
        Formula n = V("n"), N = V("N"), x = V("x"), k = V("k");
        var exponent = Subtract(Subtract(N, D(1)), Val(k));
        var quotient = Call("div", Val(x), Pow(Add(n, D(1)), exponent));
        var value = Call("mod", quotient, Add(n, D(1)));
        return All(n, Nat(), All(N, Nat(), All(x, Chain(n, N), All(k, Fin(N),
            Eqn(Call("digit", x, k), FinValue(value, Add(n, D(1))))))));
    }

    private static Formula QnumFormula() => All(GammaLower, Real(), All(V("t"), Real(),
        Eqn(Call("qnum", GammaLower, V("t")),
            FracOf(Call("sin", Mul(GammaLower, V("t"))), Call("sin", GammaLower)))));

    private static Formula QFormula() => All(GammaLower, Real(),
        Eqn(Call("q", GammaLower), Add(RC(Call("cos", GammaLower)),
            Mul(Named("I"), RC(Call("sin", GammaLower))))));

    private static Formula GammaFormula() => Eqn(new Formula.Subscript(GammaLower, D(0)),
        Call("arccos", FracOf(D(4), D(5))));

    private static Formula WeightFormula() => All(V("n"), Nat(), All(V("i"), Fin(Add(V("n"), D(1))),
        Eqn(Call("weight", V("n"), V("i")),
            Subtract(NR(Val(V("i"))), FracOf(NR(V("n")), D(2))))));

    private static Formula EFormula()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        var coefficient = RC(SqrtOf(Mul(Call("qnum", GammaLower, NR(Subtract(n, Val(j)))),
            Call("qnum", GammaLower, NR(Add(Val(j), D(1)))))));
        return All(n, Nat(), All(GammaLower, Real(), All(i, Fin(Add(n, D(1))),
            All(j, Fin(Add(n, D(1))), Eqn(At(Call("E", n, GammaLower), i, j),
                Ite(Eqn(Val(i), Add(Val(j), D(1))), coefficient, D(0)))))));
    }

    private static Formula FFormula()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        var coefficient = RC(SqrtOf(Mul(Call("qnum", GammaLower, NR(Val(j))),
            Call("qnum", GammaLower, NR(Add(Subtract(n, Val(j)), D(1)))))));
        return All(n, Nat(), All(GammaLower, Real(), All(i, Fin(Add(n, D(1))),
            All(j, Fin(Add(n, D(1))), Eqn(At(Call("F", n, GammaLower), i, j),
                Ite(Eqn(Val(j), Add(Val(i), D(1))), coefficient, D(0)))))));
    }

    private static Formula KFormula(bool inverse)
    {
        Formula n = V("n"), i = V("i");
        var angle = Mul(GammaLower, Call("weight", n, i));
        if (inverse) angle = Negated(angle);
        return All(n, Nat(), All(GammaLower, Real(),
            Eqn(Call(inverse ? "Kinv" : "K", n, GammaLower),
                Call("diagonal", LambdaOf(i, Fin(Add(n, D(1))), Call("q", angle))))));
    }

    private static Formula TensorCasimirFormula()
    {
        Formula n = V("n"), de = V("de"), df = V("df"), dk = V("dk"), dki = V("dki");
        Formula e = Call("E", n, GammaLower), f = Call("F", n, GammaLower),
            k = Call("K", n, GammaLower), ki = Call("Kinv", n, GammaLower);
        var coefficient = RC(FracOf(Call("cos", GammaLower),
            Mul(D(4), Pow(Call("sin", GammaLower), D(2)))));
        var value = Subtract(Smul(FracOf(D(1), D(2)), Add(Mul(de, df), Mul(df, de))),
            Smul(coefficient, Mul(Parenthesized(Subtract(dk, dki)), Parenthesized(Subtract(dk, dki)))));
        return All(n, Nat(), All(GammaLower, Real(), Eqn(Call("tensorCasimir", n, GammaLower),
            Let("de", Add(Tensor(e, ki), Tensor(k, e)),
                Let("df", Add(Tensor(f, ki), Tensor(k, f)),
                    Let("dk", Tensor(k, k), Let("dki", Tensor(ki, ki), value)))))));
    }

    private static Formula CasimirValueFormula() => All(GammaLower, Real(), All(V("l"), Nat(),
        Eqn(Call("casimirValue", GammaLower, V("l")),
            Mul(Call("qnum", GammaLower, NR(V("l"))),
                Call("qnum", GammaLower, NR(Add(V("l"), D(1))))))));

    private static Formula OrderedProductFormula()
    {
        Formula f = V("f"), k = V("k");
        var equations = And(Eqn(Call("orderedProduct", f, D(0)), D(1)),
            All(k, Nat(), Eqn(Call("orderedProduct", f, Add(k, D(1))),
                Mul(Call("orderedProduct", f, k), At(f, k)))));
        return All(Alpha, Types(), Arrow(Instance("Monoid", Alpha),
            All(f, Arrow(Nat(), Alpha), equations)));
    }

    private static Formula ProjectorFormula()
    {
        Formula n = V("n"), s = V("s"), l = V("l");
        var denominator = Mul(RC(Call("qnum", GammaLower, Subtract(NR(s), NR(l)))),
            RC(Call("qnum", GammaLower, NR(Add(Add(s, l), D(1))))));
        var factor = Smul(Call("inv", denominator),
            Subtract(Call("tensorCasimir", n, GammaLower),
                Smul(RC(Call("casimirValue", GammaLower, l)), D(1))));
        return All(n, Nat(), All(s, Nat(), All(GammaLower, Real(),
            Eqn(Call("projector", n, s, GammaLower),
                Call("orderedProduct", LambdaOf(l, Nat(), Ite(Ne(l, s), factor, D(1))), Add(n, D(1)))))));
    }

    private static Formula SiteOperatorFormula()
    {
        Formula R = V("R"), n = V("n"), N = V("N"), m = V("m"), P = V("P"),
            x = V("x"), y = V("y"), k = V("k");
        var first = FinValue(Val(m), N);
        var second = FinValue(Add(Val(m), D(1)), N);
        var agrees = All(k, Fin(N), Arrow(Ne(k, first), Arrow(Ne(k, second),
            Eqn(Call("digit", x, k), Call("digit", y, k)))));
        var entry = At(P, Pair(Call("digit", x, first), Call("digit", x, second)),
            Pair(Call("digit", y, first), Call("digit", y, second)));
        var equality = Eqn(At(Call("siteOperator", m, P), x, y), Ite(agrees, entry, D(0)));
        return All(R, Types(), Arrow(Instance("Zero", R), All(n, Nat(), All(N, Nat(),
            All(m, Fin(Subtract(N, D(1))), All(P, TwoSite(n, R),
                All(x, Chain(n, N), All(y, Chain(n, N), equality))))))));
    }

    private static Formula HamiltonianFormula()
    {
        Formula n = V("n"), s = V("s"), N = V("N"), a = V("a"), m = V("m");
        var term = Smul(RC(At(a, m)), Call("siteOperator", m, Call("projector", n, s, GammaLower)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(m, Sp, Colon, Sp, Fin(Subtract(N, D(1))))),
            Sp, Parenthesized(term));
        return All(n, Nat(), All(s, Nat(), All(N, Nat(), All(GammaLower, Real(),
            All(a, Arrow(Fin(Subtract(N, D(1))), Real()),
                Eqn(Call("hamiltonian", n, s, N, GammaLower, a), sum))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = V("n"), s = V("s"), N = V("N"), l = V("l"), a = V("a"),
            m = V("m"), v = V("v"), z = V("z");
        var denominator = Mul(Call("qnum", GammaLower, Subtract(NR(s), NR(l))),
            Call("qnum", GammaLower, NR(Add(Add(s, l), D(1)))));
        var nonvanishing = All(l, Nat(), Arrow(Le(l, n), Arrow(Ne(l, s), Ne(denominator, D(0)))));
        var eigenpair = Eqn(Call("mulVec", Call("hamiltonian", n, s, N, GammaLower, a), v), Smul(z, v));
        var spectral = All(v, Arrow(Chain(n, N), Complex()), All(z, Complex(),
            Arrow(Ne(v, D(0)), Arrow(eigenpair, Eqn(Call("im", z), D(0))))));
        var couplings = All(a, Arrow(Fin(Subtract(N, D(1))), Real()),
            Arrow(All(m, Fin(Subtract(N, D(1))), Lt(D(0), At(a, m))), spectral));
        var body = All(n, Nat(), All(s, Nat(), All(N, Nat(), All(GammaLower, Real(),
            Arrow(Le(D(1), n), Arrow(Le(s, n), Arrow(Le(D(2), N),
                Arrow(Lt(D(0), Abs(GammaLower)), Arrow(Lt(Mul(NR(n), Abs(GammaLower)), Pi),
                    Arrow(nonvanishing, couplings))))))))));
        return IffOf(Named("claim"), body);
    }
}
