using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class MarkovMpembaTripletRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/avitanfactorgelbwaserklimovsky2026mpembatriplets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four reversible energy levels exhibit the Mpemba effect although every triplet fails the proposed three-level condition.",
        H("A four-level counterexample to the Mpemba triplet conjecture"), Blocks(
            Paragraph(Text(
                "The states are Fin N, the indices 0 through N − 1. Energies, inverse temperatures and transition "
                    + "rates are real. The entry a(i,j) is the rate from j to i, and probability vectors are columns. "
                    + "All sums over Fin N range over the entire finite state space. The definitions allow arbitrary "
                    + "real arguments; positivity, ordering and detailed balance are hypotheses of the conjecture.")),
            Node("generator", "The continuous-time rate matrix", GeneratorFormula(),
                "Equation (1) places a(i,j) off the diagonal and the negative total rate leaving j on the diagonal. "
                    + "The conditional summand removes the self-transition. Each column sums to zero, as required "
                    + "for the population equation dp/dt = M p."),
            Node("DetailedBalance", "Balance at the bath temperature", DetailedBalanceFormula(),
                "The rate ratio between distinct levels is the Boltzmann factor at bath inverse temperature βb. "
                    + "This is the detailed-balance relation accompanying Eq. (1). No condition is imposed on a(i,i)."),
            Node("TripletCondition", "The two alternatives of the three-level condition", TripletFormula(),
                "For ordered indices i < j < k, identify the lowest, middle and highest levels with i, j and k. "
                    + "Write x = exp(−βb(E(j) − E(i))), y = exp(−βb(E(k) − E(j))) and "
                    + "κ = (a(i,k) + a(j,k))/(a(i,j)(1 + x)); the displayed condition substitutes these expressions. "
                    + "The first alternative of condition (3) uses κ ≥ 1 and the second uses κ ≤ 1. "
                    + "At κ = 1 either strict inequality suffices. Every triplet uses the original rates a, "
                    + "without recalculating rates after removing other levels. Ordering of the indices is required "
                    + "by the conjecture, rather than by this definition."),
            Node("IsSlowMode", "A simple slowest nonzero mode", SlowModeFormula(),
                "The number λ is negative and ℓ is a nonzero left eigenvector. Every real eigenvalue of M is "
                    + "zero or at most λ, and every left eigenvector at λ is a scalar multiple of ℓ. "
                    + "Matrix.vecMul is multiplication of a row vector by a matrix; Matrix.mulVec multiplies "
                    + "a matrix by a column vector. The dot denotes scalar multiplication in the eigenvector equations. "
                    + "For a detailed-balance rate matrix these conditions select the slowest nonzero mode "
                    + "in the decomposition (2), with a one-dimensional left eigenspace. Its coefficient for an "
                    + "initial Gibbs state is ℓ dotted with that state, up to a fixed nonzero normalization."),
            Describe.Lean(
                DescribeId.Create("mpemba-triplet-mpembaeffect"),
                DeclarationHandle.Create(Prefix + "MpembaEffect"),
                H("A smaller slow-mode coefficient farther from the bath"),
                StatementSource.FromAuthor(Disp(MpembaFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "There are two initial inverse temperatures on the same side of βb. "
                            + "The first is farther from the bath and has a strictly smaller absolute slow-mode "
                            + "coefficient than the second. The first alternative describes cooling, with "
                            + "0 < β₁ < β₂ < βb; the second describes heating, with βb < β₂ < β₁. "
                            + "These are exactly the two alternatives in the definition. The coefficient uses "
                            + "the Gibbs distribution GlauberRelaxationOrderRefutation.gibbs, whose formula is:")),
                    new DocumentBlock.DisplayFormula(GibbsFormula()),
                    Paragraph(Text(
                        "The denominator normalizes the Boltzmann weights over all N states. "
                            + "The dot product in the preceding statement sums ℓ(i) times the Gibbs probability "
                            + "of i. For the simple slow mode of Eq. (2), comparing these absolute dot products "
                            + "compares the absolute coefficients independently of the eigenvector normalization."))),
                DescribeRole.Definition),
            Node("claim", "The finite-temperature triplet conjecture", ClaimFormula(),
                "The conjecture on page 4 asserts that failure of condition (3) in every triplet excludes "
                    + "the Mpemba effect in the full system. Here N is at least three, E is strictly increasing, "
                    + "the bath inverse temperature is positive, and all rates between distinct levels are positive "
                    + "and satisfy detailed balance. StrictMono E means E(i) < E(j) whenever i < j. "
                    + "For every ordered triplet neither alternative of condition (3) holds. The conclusion "
                    + "excludes the two-temperature effect for every simple slowest nonzero mode of the full rate matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("mpemba-triplet-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Four levels with no qualifying triplet and a Mpemba effect"),
                StatementSource.FromAuthor(Disp(Not(Q("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take four levels with energies E = (0,1,2,64)·log 16 and bath inverse temperature βb = 1. "
                            + "Put r = 16⁻⁶⁴ and μ = 2(125 + 1024r)/(15(273 + 256r)). Then "
                            + "0 < r ≤ 1/4096 and 3/50 < μ < 1/16. Define "
                            + "A = 47/48 − μ − 112r/25, B = 3/2 − 3μ/2 − 128r/25, and C = 31/20 − 15μ/8. "
                            + "The rate array, with rows and columns ordered 0,1,2,3, is "
                            + "[[0,A,B,C],[A/16,0,1,3/5],[B/256,1/16,0,1/10],[Cr,48r/5,128r/5,0]]. "
                            + "All its off-diagonal entries are positive. The unnormalized bath weights "
                            + "w = (1,1/16,1/256,r) satisfy a(i,j)w(j) = a(j,i)w(i), giving detailed balance.")),
                    Paragraph(Text(
                        "For each of the four triplets (0,1,2), (0,1,3), (0,2,3) and (1,2,3), put "
                            + "x = w(j)/w(i) and y = w(k)/w(j). Direct substitution gives "
                            + "a(i,k)(1 + xy/2) − a(j,k)(1 + y/2) ≤ a(i,j)(1 − x) and "
                            + "a(i,k)x ≤ a(j,k). Thus both strict rate inequalities in (3) fail in every triplet, "
                            + "regardless of which side of 1 contains κ = (a(i,k) + a(j,k))/(a(i,j)(1 + x)).")),
                    Paragraph(Text(
                        "Set g = (0,1,2/3,8/15), let 1 denote the vector with every entry one, and put ℓ = g − μ1. "
                            + "For M = generator(a), one has 1ᵀM = 0, ℓᵀM = −ℓᵀ and Mw = 0. "
                            + "The remaining real eigenvalues lie below −2. To see the bound, restrict M to "
                            + "K = {v : Σᵢv(i) = 0 and g·v = 0}, with basis (1,2,−3,0), (7,8,0,−15). "
                            + "Its two-by-two matrix has trace "
                            + "t = (−50823168r² − 60948224r − 9618245)/(7680(256r + 273)) < −4. "
                            + "For its characteristic polynomial p(z) = z² − tz + d, where d is its determinant, "
                            + "p(−2) = (6914360475648r⁴ + 14183493009408r³ + 7535913889792r² "
                            + "+ 274800737600r + 4382303125)/(960000(256r + 273)²) > 0. "
                            + "If z ≥ −2, then p(z) = p(−2) + (z + 2)(z − 2 − t) > 0. "
                            + "Every real eigenvalue other than 0 and −1 is a root of this polynomial, hence is below −2.")),
                    Paragraph(Text(
                        "Also p(−1) = (274752r + 59225)(12582912r³ + 26058752r² + 14458848r + 995875)"
                            + "/(480000(256r + 273)²) > 0. A left eigenvector at −1 is orthogonal to w "
                            + "and to both displayed basis vectors of K. These constraints make it a scalar "
                            + "multiple of ℓ. Thus −1 is the simple slowest nonzero mode.")),
                    Paragraph(Text(
                        "For x > 0, write β = log(x⁻¹)/log 16, so 16^(−β) = x. The Gibbs probabilities are "
                            + "(1,x,x²,x⁶⁴)/(1 + x + x² + x⁶⁴), and their coefficient along ℓ is "
                            + "(x + (2/3)x² + (8/15)x⁶⁴)/(1 + x + x² + x⁶⁴) − μ. "
                            + "Choose β₁ = log(1024/1023)/log 16 and β₂ = log(128/127)/log 16. "
                            + "Then 0 < β₁ < β₂ < 1, with x₁ = 1023/1024 and x₂ = 127/128. "
                            + "The displayed rational expression before subtracting μ is greater than 1/16 "
                            + "at x₁ and strictly larger at x₂. Since μ < 1/16, both coefficients are positive "
                            + "and the hotter initial state, β₁, has the smaller absolute coefficient. "
                            + "This gives a Mpemba effect although all four triplets fail (3), contradicting the conjecture."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("avitan-factor-gelbwaser-klimovsky-2026-mpemba-triplet-conjecture"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("mpemba-triplet-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => name switch
    {
        "betaB" => new Formula.Subscript(Beta, F.Id("b")),
        "beta1" => new Formula.Subscript(Beta, D(1)),
        "beta2" => new Formula.Subscript(Beta, D(2)),
        "beta" => Beta,
        "lam" => LambdaLower,
        "ell" => Ell,
        "mu" => Mu,
        _ => F.Id(name),
    };
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Indices() => Call("Fin", V("N"));
    private static Formula Vector() => new Formula.TypeArrow(Indices(), Real());
    private static Formula Rates() => new Formula.TypeArrow(Indices(), Vector());
    private static Formula MatrixType() => Call("Matrix", Indices(), Indices(), Real());
    private static Formula Size(Formula body) => All("N", Nat(), body);
    private static Formula Thermal(Formula body) => All("E", Vector(), All("betaB", Real(), body));
    private static Formula TripletIndices(Formula body) =>
        All("i", Indices(), All("j", Indices(), All("k", Indices(), body)));
    private static Formula A(string row, string column) => At(V("a"), V(row), V(column));
    private static Formula E(string index) => At(V("E"), V(index));
    private static Formula Exp(Formula value) => Call("Real.exp", value);
    private static Formula Gap(string high, string low) =>
        Exp(Negate(Mul(V("betaB"), Sub(E(high), E(low)))));
    private static Formula Gibbs(Formula beta) => Call(
        "D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs", V("E"), beta);
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), Indices())), Sp, Parenthesized(body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Q("if"), Sp, Parenthesized(condition), Sp, Q("then"), Sp,
            Parenthesized(yes), Sp, Q("else"), Sp, Parenthesized(no));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Frac(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula GeneratorFormula() => Size(All("a", Rates(),
        All("i", Indices(), All("j", Indices(), Eq(Call("generator", V("a"), V("i"), V("j")),
            Conditional(Eq(V("i"), V("j")),
                Negate(SumOver("k", Conditional(Eq(V("k"), V("j")), D(0), A("k", "j")))), A("i", "j")))))));

    private static Formula DetailedBalanceFormula() => Size(Thermal(All("a", Rates(),
        IffOf(Call("DetailedBalance", V("E"), V("betaB"), V("a")),
            All("j", Indices(), All("k", Indices(), Imp(Ne(V("j"), V("k")),
                Eq(A("j", "k"), Mul(A("k", "j"), Gap("j", "k"))))))))));

    private static Formula TripletFormula()
    {
        Formula x = Gap("j", "i");
        Formula y = Gap("k", "j");
        Formula kappa = Frac(Add(A("i", "k"), A("j", "k")), Mul(A("i", "j"), Add(D(1), x)));
        Formula first = And(Le(D(1), kappa), Lt(Mul(A("i", "j"), Sub(D(1), x)),
            Sub(Mul(A("i", "k"), Add(D(1), Frac(Mul(x, y), D(2)))),
                Mul(A("j", "k"), Add(D(1), Frac(y, D(2)))))));
        Formula second = And(Le(kappa, D(1)), Lt(A("j", "k"), Mul(A("i", "k"), x)));
        return Size(Thermal(All("a", Rates(), TripletIndices(
            IffOf(Call("TripletCondition", V("E"), V("betaB"), V("a"), V("i"), V("j"), V("k")),
                Or(first, second))))));
    }

    private static Formula SlowModeFormula()
    {
        Formula spectrum = All("mu", Real(), All("v", Vector(), Imp(Ne(V("v"), D(0)),
            Imp(Eq(Call("Matrix.mulVec", V("M"), V("v")), Mul(V("mu"), V("v"))),
                Or(Eq(V("mu"), D(0)), Le(V("mu"), V("lam")))))));
        Formula simple = All("v", Vector(),
            Imp(Eq(Call("Matrix.vecMul", V("v"), V("M")), Mul(V("lam"), V("v"))),
                Some("c", Real(), Eq(V("v"), Mul(V("c"), V("ell"))))));
        Formula conditions = And(Lt(V("lam"), D(0)), And(Ne(V("ell"), D(0)),
            And(Eq(Call("Matrix.vecMul", V("ell"), V("M")), Mul(V("lam"), V("ell"))),
                And(spectrum, simple))));
        return Size(All("M", MatrixType(), All("lam", Real(), All("ell", Vector(),
            IffOf(Call("IsSlowMode", V("M"), V("lam"), V("ell")), conditions)))));
    }

    private static Formula MpembaFormula()
    {
        Formula cooling = And(Lt(D(0), V("beta1")),
            And(Lt(V("beta1"), V("beta2")), Lt(V("beta2"), V("betaB"))));
        Formula heating = And(Lt(V("betaB"), V("beta2")), Lt(V("beta2"), V("beta1")));
        Formula coefficient1 = new Formula.Absolute(Call("dotProduct", V("ell"), Gibbs(V("beta1"))));
        Formula coefficient2 = new Formula.Absolute(Call("dotProduct", V("ell"), Gibbs(V("beta2"))));
        return Size(Thermal(All("ell", Vector(), IffOf(Call("MpembaEffect", V("E"), V("betaB"), V("ell")),
            Some("beta1", Real(), Some("beta2", Real(),
                And(Or(cooling, heating), Lt(coefficient1, coefficient2))))))));
    }

    private static Formula GibbsFormula() => Size(All("E", Vector(), All("beta", Real(),
        All("i", Indices(), Eq(At(Gibbs(V("beta")), V("i")),
            Frac(Exp(Mul(Negate(V("beta")), E("i"))),
                SumOver("j", Exp(Mul(Negate(V("beta")), E("j"))))))))));

    private static Formula ClaimFormula()
    {
        Formula allTriplets = TripletIndices(Imp(Lt(V("i"), V("j")), Imp(Lt(V("j"), V("k")),
            Not(Call("TripletCondition", V("E"), V("betaB"), V("a"), V("i"), V("j"), V("k"))))));
        Formula conclusion = All("lam", Real(), All("ell", Vector(),
            Imp(Call("IsSlowMode", Call("generator", V("a")), V("lam"), V("ell")),
                Not(Call("MpembaEffect", V("E"), V("betaB"), V("ell"))))));
        Formula[] hypotheses =
        [
            Le(D(3), V("N")),
            Call("StrictMono", V("E")),
            Lt(D(0), V("betaB")),
            All("i", Indices(), All("j", Indices(), Imp(Ne(V("i"), V("j")), Lt(D(0), A("i", "j"))))),
            Call("DetailedBalance", V("E"), V("betaB"), V("a")),
            allTriplets,
        ];
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            conclusion = Imp(hypotheses[index], conclusion);
        return IffOf(Q("claim"), Size(Thermal(All("a", Rates(), conclusion))));
    }
}
