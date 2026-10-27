using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class BernoulliNoiseWalkGaussianLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Asymptotics/wangwangtangren2018bernoulliwalk");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every unit localized quantum Bernoulli noise state has the standard Gaussian scaling limit.",
        H("The Gaussian limit for localized quantum Bernoulli noise walks"),
        Blocks(
            Paragraph(Text(
                "The Hilbert space is ObserverHilbertSpace (Finset ℕ), the complex space ℓ² over finite subsets of ℕ. "
                + "Its coordinate unit vectors correspond to the source's orthonormal basis Zσ of the space h of square-integrable Bernoulli functionals "
                + "(Section 2, equation (7)). This identification transports the source's operators and localized initial states to their coefficient sequences.")),
            Definition("annihilation", "Annihilation at a coordinate", CoordinateFormula("annihilation", false),
                "The annihilation operator removes k from a basis index that contains it and sends every other basis vector to zero "
                + "(Lemma 1, equation (8)). In coefficient form, the output at σ reads the input at σ symmetric-difference {k} when k is absent from σ. "
                + "The displayed coordinate identity specifies the continuous complex-linear operator uniquely."),
            Definition("creation", "Creation at a coordinate", CoordinateFormula("creation", true),
                "The creation operator adds k to a basis index that does not contain it and sends every other basis vector to zero "
                + "(Lemma 2, equation (9)). In coefficient form, the output at σ reads the input at σ symmetric-difference {k} when k belongs to σ. "
                + "It is the adjoint of annihilation on this Hilbert space."),
            Definition("R", "The right operator", OperatorFormula("R", false),
                "The right operator is half the sum of creation, annihilation and the identity, as in Lemma 5. "
                + "It is the orthogonal projection onto the positive eigenspace of the coordinate flip."),
            Definition("L", "The left operator", OperatorFormula("L", true),
                "The left operator is half the sum of creation and annihilation minus the identity, as in Lemma 5. "
                + "Its negative is the orthogonal projection onto the negative eigenspace of the coordinate flip; this sign is retained in the walk recursion."),
            Definition("walk", "The walk with a localized initial vector", WalkFormula(),
                "At time zero the state equals φ at the integer position zero and vanishes at all other positions "
                + "(equation (53)). The successor step is equation (16): the right operator acts on the state at x minus one, "
                + "and the left operator acts on the state at x plus one. The definition allows every vector φ; normalization is imposed in the limit theorem."),
            Definition("walkLaw", "The scaled position measure", LawFormula(),
                "The mass at the scaled position x divided by the square root of n is the squared norm of the walk amplitude at x "
                + "(Section 3; the proof of Theorem 20, equations (64) and (67)). Only the integer interval from minus n to n can carry mass. "
                + "The total mass is the squared norm of φ, so a unit vector gives a probability measure. "
                + "At n equal to zero, real division by zero places the initial mass at zero as well."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Weak convergence to the standard Gaussian"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For each unit vector φ, the scaled position measures converge against every bounded continuous real function to the standard Gaussian. "
                        + "The initial vector is arbitrary in the whole Hilbert space. The convergence is asserted for each fixed φ and test function f; "
                        + "it does not assert uniformity over initial vectors.")),
                    Paragraph(Text(
                        "Let Tₖ be the coordinate flip, sending the coefficient at σ to the coefficient at σ symmetric-difference {k}. "
                        + "Each flip is a self-adjoint isometric involution, and the flips commute. Creation plus annihilation equals Tₖ, "
                        + "so Rₖ = (I + Tₖ)/2 and −Lₖ = (I − Tₖ)/2 are complementary orthogonal projections. "
                        + "The recursion first shows that the amplitude vanishes outside the integer interval from minus n to n.")),
                    Paragraph(Text(
                        "For σ contained in {0,…,n−1}, let Bₙ,σ be the ordered product, starting with the identity, "
                        + "of −Lₖ when k belongs to σ and Rₖ otherwise, for k less than n. "
                        + "The vector Bₙ,σφ is a simultaneous flip eigenvector, with eigenvalue minus one at the coordinates in σ and plus one at the other coordinates below n. "
                        + "Distinct subsets therefore give orthogonal vectors. Summing Bₙ,σφ over all such subsets gives φ.")),
                    Paragraph(Text(
                        "The displacement associated to σ is n − 2|σ|, an integer between minus n and n. "
                        + "Induction in the walk recursion expresses its amplitude at x as the sum of (−1)^|σ| Bₙ,σφ over subsets with that displacement. "
                        + "Orthogonality removes the cross terms: the squared amplitude at x is the sum of the squared norms of Bₙ,σφ over the same subsets. "
                        + "The orthogonal resolution of φ makes the sum of these squared norms equal to the squared norm of φ. "
                        + "This proves that every scaled measure associated to a unit vector is a probability measure.")),
                    Paragraph(Text(
                        "For real u define U₀(u) = I and Uₙ₊₁(u) = (cos(u) I + i sin(u) Tₙ)Uₙ(u). "
                        + "The one-step factor equals exp(iu)Rₙ − exp(−iu)Lₙ. Expanding the product gives "
                        + "Uₙ(u)φ as the sum of exp(iu(n − 2|σ|))Bₙ,σφ. "
                        + "The orthogonal resolution also gives ⟨φ,Bₙ,σφ⟩ = ‖Bₙ,σφ‖². "
                        + "Integration of the atomic position measure and regrouping by displacement now identify its characteristic function at t with "
                        + "⟨φ,Uₙ(t/√n)φ⟩. Expanding the inner product of a one-step factor shows that the mixed terms cancel "
                        + "by self-adjointness of Tₖ, while cos²(u) + sin²(u) = 1. Thus every Uₙ(u) preserves norms.")),
                    Paragraph(Text(
                        "Suppose η has nonzero coefficients only at subsets of {0,…,m−1}. The first m flip factors preserve this support. "
                        + "At every later step the flipped contribution has zero inner product with η. Consequently, for n at least m, "
                        + "⟨η,Uₙ(u)η⟩ = cos(u)^(n−m)⟨η,Uₘ(u)η⟩. "
                        + "For the symmetric probability measure giving mass one half to each of 1 and −1, the mean is zero, the second moment is one, "
                        + "and the characteristic function is cos(u). Its central limit theorem gives cos(t/√n)^n → exp(−t²/2). "
                        + "The parameter t/√n tends to zero. Continuity of the finite product Uₘ at zero, where Uₘ(0) = I, "
                        + "and division by cos(t/√n)^m give ⟨η,Uₙ(t/√n)η⟩ → ‖η‖² exp(−t²/2).")),
                    Paragraph(Text(
                        "Finite sums of coordinate unit vectors are dense in ℓ². For any finite set of coefficient indices, "
                        + "choose m greater than every natural number in their union; the corresponding finite vector has the required support. "
                        + "Norm preservation and the inner-product inequality give "
                        + "|⟨φ,Uₙ(u)φ⟩ − ⟨η,Uₙ(u)η⟩| ≤ (‖φ‖ + ‖η‖)‖φ − η‖, uniformly in n and u. "
                        + "Given ε positive, take ‖φ − η‖ < δ with δ = min(1,ε/12). Since ‖φ‖ = 1, one has ‖η‖ ≤ 2 and "
                        + "|‖η‖² − 1| ≤ 3‖φ − η‖. The Gaussian factor has norm at most one. "
                        + "The two approximation errors are therefore bounded by 3‖φ − η‖ each, and the finite-vector limit eventually bounds the middle error by ε/3. "
                        + "Their sum is less than ε, proving the Gaussian characteristic-function limit for every unit vector φ.")),
                    Paragraph(Text(
                        "Regard the scaled measures and the standard Gaussian as probability measures. "
                        + "The characteristic-function criterion for weak convergence applies at every real frequency, "
                        + "using the standard Gaussian characteristic function exp(−t²/2). "
                        + "The characterization of weak convergence by integrals of bounded continuous real functions then gives exactly the displayed conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wang-wang-tang-ren-2018-bernoulli-noise-walk-gaussian-limit"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name == "walkLaw" ? "walk-law" : name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CoordinateFormula(string name, bool present)
    {
        Formula membership = new Formula.Relation(X("k"), FormulaRelationOperator.MemberOf, SigmaLower);
        Formula condition = present ? membership : new Formula.Not(Parenthesized(membership));
        Formula flipped = At(Qualified("symmDiff"), SigmaLower, new Formula.SetLiteral([X("k")]));
        return All("k", Naturals, All("φ", HilbertSpace, All("σ", Finsets,
            Equal(At(Local(name), X("k"), Varphi, SigmaLower),
                At(Qualified("ite"), condition, At(Varphi, flipped), Typed(D(0), Complexes))))));
    }

    private static Formula OperatorFormula(string name, bool subtractIdentity)
    {
        Formula pair = Add(At(Local("creation"), X("k")), At(Local("annihilation"), X("k")));
        Formula identity = At(Qualified("ContinuousLinearMap", "id"), Complexes, HilbertSpace);
        Formula body = subtractIdentity ? Subtract(pair, identity) : Add(pair, identity);
        return All("k", Naturals,
            Equal(Typed(At(Local(name), X("k")), OperatorType),
                Smul(Typed(new Formula.Fraction(D(1), D(2)), Complexes), body)));
    }

    private static Formula WalkFormula()
    {
        Formula initial = LambdaOf("x", Integers,
            At(Qualified("ite"), Equal(X("x"), Typed(D(0), Integers)), Varphi, Typed(D(0), HilbertSpace)));
        Formula step = LambdaOf("n", Naturals, LambdaOf("ψ", Arrow(Integers, HilbertSpace), LambdaOf("x", Integers,
            Add(At(Local("R"), X("n"), At(Psi, Subtract(X("x"), Typed(D(1), Integers)))),
                At(Local("L"), X("n"), At(Psi, Add(X("x"), Typed(D(1), Integers))))))));
        return All("φ", HilbertSpace,
            Equal(Typed(At(Local("walk"), Varphi), Arrow(Naturals, Arrow(Integers, HilbertSpace))),
                At(Qualified("Nat", "rec"), initial, step)));
    }

    private static Formula LawFormula()
    {
        Formula interval = At(Qualified("Finset", "Icc"),
            new Formula.Negate(Cast("Nat", X("n"), Integers)), Cast("Nat", X("n"), Integers));
        Formula weight = At(Qualified("ENNReal", "ofReal"),
            new Formula.Power(new Formula.Norm(At(Local("walk"), Varphi, X("n"), X("x"))), D(2)));
        Formula location = new Formula.Fraction(Cast("Int", X("x"), Reals),
            At(Qualified("Real", "sqrt"), Cast("Nat", X("n"), Reals)));
        Formula summand = Smul(weight, At(Qualified("Measure", "dirac"), location));
        return All("φ", HilbertSpace, All("n", Naturals,
            Equal(Typed(At(Local("walkLaw"), Varphi, X("n")), At(Qualified("Measure"), Reals)),
                Seq(new Formula.Subscript(Sum, Seq(X("x"), Sp, InMacro, Sp, interval)), Sp, Parenthesized(summand)))));
    }

    private static Formula ResultFormula() => All("φ", HilbertSpace,
        Imp(Equal(new Formula.Norm(Varphi), Typed(D(1), Reals)),
            All("f", At(Qualified("BoundedContinuousFunction"), Reals, Reals),
                At(Qualified("Filter", "Tendsto"),
                    LambdaOf("n", Naturals, Integral(At(Local("walkLaw"), Varphi, X("n")))),
                    Qualified("Filter", "atTop"),
                    At(Qualified("nhds"), Integral(At(Qualified("ProbabilityTheory", "gaussianReal"),
                        Typed(D(0), Reals), Typed(D(1), Qualified("NNReal")))))))));

    private static Formula Integral(Formula measure) => Seq(
        Int, Sp, Typed(X("y"), Reals), Comma, Sp, At(X("f"), X("y")), Sp,
        Qualified("d"), Parenthesized(measure));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Dynamics", "BernoulliNoiseWalkGaussianLimit", name);
    private static Formula HilbertSpace => At(Qualified("ObserverHilbertSpace"), Finsets);
    private static Formula Finsets => At(Qualified("Finset"), Naturals);
    private static Formula OperatorType => Seq(HilbertSpace, Sp, new Formula.Subscript(To, Seq(X("L"), OpenBracket, Complexes, CloseBracket)), Sp, HilbertSpace);
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula Integers => Seq(Mathbb, Grp(X("Z")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula X(string name) => name switch
    {
        "φ" => Varphi,
        "ψ" => Psi,
        "σ" => SigmaLower,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Cast(string domain, Formula value, Formula type) => Typed(At(Qualified(domain, "cast"), value), type);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Smul(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Imp(Formula hypothesis, Formula conclusion) => new Formula.Logic(Parenthesized(hypothesis), FormulaLogicOperator.Implies, Parenthesized(conclusion));
}
