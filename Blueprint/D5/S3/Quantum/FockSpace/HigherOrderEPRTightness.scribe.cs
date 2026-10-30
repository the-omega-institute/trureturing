using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class HigherOrderEPRTightnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/FockSpace/HigherOrderEPRTightness";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/shchukinvanloock2016higherorderepr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero higher-order EPR bound is tight for both signs at every positive order.",
        H("Tightness of the higher-order EPR bound"),
        Blocks(
            Definition("normsq", "normSq", "Squared occupation-basis norm", NormSqFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A finitely supported complex function on pairs of natural occupation numbers represents a two-mode state. "
                    + "Its squared norm is the finite sum of the squared absolute values of its amplitudes. "
                    + "This is the usual occupation-basis norm used in the source's normalization equation "
                    + "in bip-ent2.tex, lines 925–934, restricted here to finite support."),
            Definition("annihilatea", "annihilateA", "Annihilation in the first mode", AnnihilateAFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The nth power of first-mode annihilation sends the basis state at p to the state with n fewer first-mode quanta, "
                    + "multiplied by the square root of the falling factorial. It vanishes when the first occupation is less than n. "
                    + "Finsupp.linearCombination extends this basis action complex linearly. "
                    + "These are the annihilation powers in the source's higher-order expression, bip-ent2.tex, lines 914–922. "
                    + "Both factorials are cast from natural to real numbers before division, and the real square root is then included in the complex numbers."),
            Definition("createb", "createB", "Creation in the second mode", CreateBFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The nth power of second-mode creation adds n to the second occupation and multiplies the amplitude by the square root of the rising factorial. "
                    + "Its complex linear extension acts on all finitely supported states. "
                    + "This is the creation power in bip-ent2.tex, lines 914–922. "
                    + "As for annihilation, the factorial ratio is real and its square root is explicitly included in the complex numbers."),
            Definition("claim", "claim", "Tightness for every positive order", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every positive natural order n, either complex sign σ, and every positive real ε, "
                    + "there is a finitely supported state ψ of squared norm one whose image under the signed sum of the two operator powers has squared norm below ε. "
                    + "The source states the nonnegative bound in bip-ent2.tex, lines 914–924, and asks for its tightness at lines 961–963. "
                    + "The formula expresses that question using finite occupation-basis states and a squared norm. "
                    + "It makes no assertion about Gaussian states or about whether zero can be attained."),
            Describe.Lean(
                DescribeId.Create("higher-order-epr-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Normalized finite states approach zero"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Multiplication of a state by a complex scalar multiplies its squared norm by the squared absolute value of that scalar. "
                            + "For a finite sum of single-site states at distinct occupation pairs, the squared norm is the sum of the squared absolute values of their amplitudes.")),
                    Paragraph(Text(
                        "Write Hₖ for the kth harmonic number, regarded as real. For a positive natural m set fₖ = 1 − Hₖ/Hₘ "
                            + "and cₖ = √((nk)!/(nk+n−1)!). Let v be the finite sum, for 0 ≤ k ≤ m, "
                            + "of the basis states at (nk+n−1,nk) with complex amplitudes (−σ)ᵏfₖcₖ. "
                            + "For positive r the factorial identity r! = r(r−1)! gives "
                            + "√(t!/(r−1)!) √(r!/t!) = √r. "
                            + "Applying this identity to the two operator actions shows that annihilation of the term at k+1 "
                            + "and creation of the term at k both reach (n(k+1)−1,n(k+1)), with the same factorial factor √(n(k+1)).")),
                    Paragraph(Text(
                        "Annihilation kills the initial term because its first occupation is n−1, and fₘ = 0 removes the final creation term. "
                            + "Thus annihilateA n v + σ • createB n v is the sum, for 0 ≤ k < m, "
                            + "of single-site states at (n(k+1)−1,n(k+1)) with amplitudes "
                            + "(−σ)ᵏ⁺¹√(n(k+1))(fₖ₊₁−fₖ). "
                            + "The harmonic recurrence gives fₖ₊₁−fₖ = −1/((k+1)Hₘ). "
                            + "Squaring the real factors and summing gives "
                            + "∑ₖ₌₀ᵐ⁻¹ n(k+1)(fₖ₊₁−fₖ)² = (n/Hₘ²)∑ₖ₌₀ᵐ⁻¹ 1/(k+1) = n/Hₘ.")),
                    Paragraph(Text(
                        "Because n is positive, the occupation pairs of v are distinct. The k = 0 term has squared amplitude 1/(n−1)!, "
                            + "so Z = normSq v is at least 1/(n−1)! and is strictly positive. "
                            + "The output occupation pairs are also distinct. For σ equal to 1 or −1, the factors (−σ)ᵏ⁺¹ have absolute value one. "
                            + "The preceding sum therefore proves that the squared norm of the unnormalized output is exactly n/Hₘ.")),
                    Paragraph(Text(
                        "The harmonic numbers are unbounded: the partial sums of 1/(k+1) tend to positive infinity. "
                            + "Hence for every real b there is a natural m at least one with Hₘ > b. "
                            + "For any state v with positive squared norm Z, multiplication by the real scalar 1/√Z, included in the complex numbers, "
                            + "produces a state ψ of squared norm one. Linearity of both operators and the squared-norm scaling identity "
                            + "show that the squared norm of its output is the squared norm of the output of v divided by Z.")),
                    Paragraph(Text(
                        "Now fix n ≥ 1, σ equal to either sign, and ε > 0. Choose m ≥ 1 with Hₘ > n!/ε and form the finite state v above. "
                            + "Its lower norm bound permits normalization. The resulting ψ has squared norm one and output squared norm n/(HₘZ). "
                            + "Using Z ≥ 1/(n−1)! and n! = n(n−1)! gives n/(HₘZ) ≤ n!/Hₘ < ε. "
                            + "This establishes the stated approximation for every order and both signs."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shchukin-van-loock-2016-higher-order-epr-tightness"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("higher-order-epr-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NormSqFormula() => All("ψ", StateType(),
        Equal(Typed(LocalCall("normSq", Psi), Reals()),
            At(Qualified("Finsupp", "sum"), Psi,
                At(Qualified("Function", "const"), PairType(),
                    LambdaOf("z", Complexes(), new Formula.Power(new Formula.Norm(X("z")), D(2)))))));

    private static Formula AnnihilateAFormula()
    {
        Formula p = X("p");
        Formula first = At(Qualified("Prod", "fst"), p);
        Formula second = At(Qualified("Prod", "snd"), p);
        Formula lowered = Subtract(first, X("n"));
        Formula weight = ComplexRoot(new Formula.Fraction(
            RealCast(Factorial(first)), RealCast(Factorial(lowered))));
        Formula basis = At(Qualified("Finsupp", "single"), Pair(lowered, second), weight);
        Formula action = At(Qualified("ite"), LE(X("n"), first), basis, Typed(D(0), StateType()));
        return All("n", Naturals(), Equal(LocalCall("annihilateA", X("n")),
            At(Qualified("Finsupp", "linearCombination"), Complexes(), LambdaOf("p", PairType(), action))));
    }

    private static Formula CreateBFormula()
    {
        Formula p = X("p");
        Formula first = At(Qualified("Prod", "fst"), p);
        Formula second = At(Qualified("Prod", "snd"), p);
        Formula raised = Add(second, X("n"));
        Formula weight = ComplexRoot(new Formula.Fraction(
            RealCast(Factorial(raised)), RealCast(Factorial(second))));
        Formula action = At(Qualified("Finsupp", "single"), Pair(first, raised), weight);
        return All("n", Naturals(), Equal(LocalCall("createB", X("n")),
            At(Qualified("Finsupp", "linearCombination"), Complexes(), LambdaOf("p", PairType(), action))));
    }

    private static Formula ClaimFormula() =>
        new Formula.Logic(Local("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula sign = new Formula.Logic(Equal(SigmaLower, Typed(D(1), Complexes())), FormulaLogicOperator.Or,
            Equal(SigmaLower, new Formula.Negate(Typed(D(1), Complexes()))));
        Formula output = Add(LocalCall("annihilateA", X("n"), Psi),
            At(Qualified("HSMul", "hSMul"), SigmaLower, LocalCall("createB", X("n"), Psi)));
        Formula conclusion = new Formula.Logic(
            Equal(LocalCall("normSq", Psi), Typed(D(1), Reals())), FormulaLogicOperator.And,
            Less(LocalCall("normSq", output), Varepsilon));
        return All("n", Naturals(), Arrow(LE(Typed(D(1), Naturals()), X("n")),
            All("σ", Complexes(), Arrow(sign, All("ε", Reals(),
                Arrow(Less(Typed(D(0), Reals()), Varepsilon), Some("ψ", StateType(), conclusion)))))));
    }

    private static Formula X(string name) => name switch
    {
        "ψ" => Psi,
        "σ" => SigmaLower,
        "ε" => Varepsilon,
        _ => F.Id(name)
    };
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "FockSpace", "HigherOrderEPRTightness", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
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
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula PairType() => Seq(Naturals(), Sp, Times, Sp, Naturals());
    private static Formula StateType() => At(Qualified("Finsupp"), Parenthesized(PairType()), Complexes());
    private static Formula Factorial(Formula value) => At(Qualified("Nat", "factorial"), value);
    private static Formula RealCast(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula ComplexRoot(Formula value) => At(Qualified("Complex", "ofReal"), At(Qualified("Real", "sqrt"), value));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula hypothesis, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(hypothesis), Parenthesized(conclusion));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
