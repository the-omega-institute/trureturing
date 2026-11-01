using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class NoisyGhzWitnessBoundGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimized GHZ witness bound is strictly below the geometric convex roof for three qutrits at noise three eighths.",
        H("A strict gap for the noisy GHZ witness bound"),
        Blocks(
            Paragraph(Text(
                "Word (Fin d) n is the computational basis Fin n → Fin d. "
                + "rankOneDensity ψ is the matrix with entries ψ(x) conjugate(ψ(y)); "
                + "IsUnitState ψ means that the sum of Complex.normSq (ψ x) is one. "
                + "readout A ψ is the real part of star ψ ⬝ᵥ (A *ᵥ ψ). "
                + "Matrix multiplication, real scalar multiplication and finite sums have these types throughout. "
                + "Nat.cast into ℝ and Complex.ofReal into ℂ display the scalar embeddings. "
                + "Subtype.val displays the inclusion of a coordinate in a chosen part of a bipartition.")),
            Node("ghz", "The GHZ amplitude", GhzFormula(),
                "GMEwitness.tex, line 284, defines the equal superposition of the d constant words, divided by √d. "
                + "The formula gives its amplitude at every computational word and defines it for all natural n and d.", true),
            Node("IsBiseparable", "Pure biseparability", BiseparableFormula(),
                "A unit vector is biseparable when its amplitudes factor across a nonempty proper set a of parties. "
                + "The two factors are arbitrary complex functions on the coordinates in a and its complement. "
                + "This expresses the pure biseparable states in GMEwitness.tex, lines 284 and 307–309.", true),
            Node("supportProjector", "The support projector", SupportFormula(),
                "The diagonal entry is one exactly on words using at most two distinct symbols. "
                + "These are the constant words and the distinct arrangements of two-symbol words in "
                + "GMEwitness.tex, lines 690–699. The cardinality in the condition is natural-valued.", true),
            Node("witnessOp", "The GHZ witness operator", WitnessFormula(),
                "GMEwitness.tex, lines 295–300, gives one dth of the support projector minus the GHZ rank-one matrix. "
                + "The coefficient is a real scalar; the natural dimension is cast to ℝ before division.", true),
            Node("noisyGhz", "The noisy GHZ matrix", NoisyFormula(),
                "GMEwitness.tex, line 284, mixes white noise with the GHZ rank-one matrix. "
                + "The identity has dimension dⁿ, and its coefficient is p/dⁿ. "
                + "The definition accepts every real p; the probability restrictions occur in claim.", true),
            Node("witnessValue", "The witness expectation", ValueFormula(),
                "GMEwitness.tex, line 301, defines the trace of the noisy GHZ matrix times the witness. "
                + "The real part gives its real-valued expectation.", true),
            Node("geometricMeasurePure", "The pure geometric measure", PureFormula(),
                "GMEwitness.tex, line 284, subtracts the largest squared biseparable overlap from one. "
                + "Here sSup is the real supremum of the squared overlaps with all biseparable unit vectors.", true),
            Node("geometricMeasure", "The finite-ensemble convex roof", RoofFormula(),
                "GMEwitness.tex, lines 284–288, extends the pure measure by the convex roof. "
                + "The infimum here ranges over all finite ensembles: nonnegative real weights summing to one, "
                + "unit pure vectors, and exact rank-one reconstruction of the matrix. "
                + "The value averaged in each ensemble is the pure geometric measure.", true),
            Node("hatE", "The convex conjugate", HatFormula(),
                "GMEwitness.tex, lines 305–309, takes both pure-state optimizations. "
                + "The single supremum ranges over every unit ψ and every biseparable φ, "
                + "of the expectation of r times the witness plus the φ rank-one matrix, minus one.", true),
            Node("epsilonO", "The optimized witness bound", EpsilonFormula(),
                "GMEwitness.tex, lines 301–305, optimizes r times the measured witness value minus the conjugate "
                + "over every real slope r. The real supremum expresses this optimization.", true),
            Node("claim", "The universal equality question", ClaimFormula(),
                "GMEwitness.tex, line 325, asks whether the optimized witness bound equals the geometric measure "
                + "of the noisy GHZ state. The displayed equality question quantifies over all natural n and d "
                + "at least three and every real noise probability p between zero and one.", false),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Three qutrits give a strict gap"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Call("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = d = 3 and p = 3/8. Write G for the GHZ rank-one projector, "
                        + "P for the support projector and Q = I − P. "
                        + "Counting the computational words gives Tr(P) = 21 and Tr(Q) = 6. The GHZ vector is unit, "
                        + "P² = P, PG = GP = G and G² = G. Thus P − G and Q are positive semidefinite. "
                        + "Consequently ρ = I/72 + (5/8)G, W = P/3 − G and Tr(ρW) = −1/3.")),
                    Paragraph(Text(
                        "The unit vector (4|000⟩ + |111⟩ + |222⟩)/√18 has P expectation one, "
                        + "G expectation 2/3, W expectation −1/3 and squared overlap 8/9 with |000⟩. "
                        + "The latter vector factors across the first party and the other two parties. "
                        + "For every unit vector the W expectation lies between −1 and 1/3, "
                        + "and every squared overlap of unit vectors is at most one. These estimates bound "
                        + "the set defining hatE at slope r above by |r|. The chosen pair belongs to this set "
                        + "and gives hatE(3,3,r) ≥ −r/3 − 1/9. "
                        + "The set defining epsilonO is nonempty by taking r = 0; "
                        + "each of its values is at most 1/9, so epsilonO(3,3,3/8) ≤ 1/9.")),
                    Paragraph(Text(
                        "For any biseparable φ, let g be its G expectation and s its P expectation. "
                        + "Choose a nonempty proper cut on which φ factors as u times v. "
                        + "Cauchy–Schwarz bounds the squared sum of its three constant-word amplitudes by "
                        + "the product of the sums of the squared constant amplitudes of u and v. "
                        + "This product is the sum over the nine words constant on each side of the cut. "
                        + "Those nine words are distinct because both parts are nonempty, and each lies "
                        + "in the support of P. Their nonnegative squared amplitudes therefore sum to at most s. "
                        + "The squared constant-word sum equals 3g, proving 3g ≤ s.")),
                    Paragraph(Text(
                        "Set B = −(2/3)W + Q/9, D = (2/3)G + (4/3)(P − G) + Q "
                        + "and T = (3/2)G + (3/4)(P − G) + Q. "
                        + "The inequality 3g ≤ s and normalization give ⟨φ,Tφ⟩ = 1 + (3g − s)/4 ≤ 1. "
                        + "Also D = (2/3)I + (2/3)(P − G) + Q/3 is positive definite, T is positive semidefinite, "
                        + "and the projector identities give DT = I. "
                        + "Apply the positive semidefinite Cauchy–Schwarz inequality for D to ψ and Tφ. "
                        + "Using DTφ = φ and the Hermitian symmetry of T gives "
                        + "|⟨φ,ψ⟩|² ≤ ⟨φ,Tφ⟩⟨ψ,Dψ⟩ ≤ ⟨ψ,Dψ⟩. "
                        + "There is a biseparable vector |000⟩, so taking the supremum over biseparable overlaps "
                        + "is legitimate. Since D + B = (10/9)I, every unit ψ satisfies "
                        + "geometricMeasurePure ψ ≥ ⟨ψ,Bψ⟩ − 1/9.")),
                    Paragraph(Text(
                        "The relations GQ = 0 and Tr(Q) = 6 give Tr(ρQ) = 1/12. "
                        + "Hence Tr(ρB) − 1/9 = −(2/3)Tr(ρW) + Tr(ρQ)/9 − 1/9 = 13/108. "
                        + "The matrix ρ is positive semidefinite with trace one, so a finite spectral ensemble exists. "
                        + "For any such ensemble, the rank-one trace identity identifies the average of "
                        + "⟨ψ,Bψ⟩ with Tr(ρB). Multiplying the pure bound by each nonnegative weight "
                        + "and summing yields an average geometric measure at least 13/108. "
                        + "Taking the infimum over the nonempty set of finite ensembles gives "
                        + "geometricMeasure ρ ≥ 13/108. "
                        + "The equality in claim at these parameters would imply 13/108 ≤ 1/9 = 12/108, "
                        + "a contradiction. No exact value of the convex roof is asserted."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("xu-et-al-2023-noisy-ghz-witness-bound-gap"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("noisy-ghz-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => name switch
    {
        "φ" => Varphi, "ψ" => Psi, "ρ" => Rho, _ => F.Id(name)
    };
    private static Formula Qualified(params string[] parts) => Seq(Operatorname,
        Grp(Seq(parts.SelectMany((part, i) => i == 0
            ? new Formula[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray())));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Qualified(name) : At(Qualified(name), args);
    private static Formula C(string owner, string name, params Formula[] args) => At(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula k) => Call("Fin", k);
    private static Formula Word => Call("Word", Fin(V("d")), V("n"));
    private static Formula Vector => Arrow(Word, Complex);
    private static Formula Matrix => Call("Matrix", Word, Word, Complex);
    private static Formula ND(Formula body) => All("n", Nat, All("d", Nat, body));
    private static Formula WithP(Formula body) => ND(All("p", Real, body));
    private static Formula RealD => Typed(C("Nat", "cast", V("d")), Real);
    private static Formula Smul(Formula a, Formula b) => C("HSMul", "hSMul", a, b);
    private static Formula RankOne(Formula x) => Call("rankOneDensity", x);
    private static Formula NormSq(Formula x) => C("Complex", "normSq", x);
    private static Formula DotOf(Formula a, Formula b) => Call("dotProduct", Call("star", a), b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Typed(V(name), type), Sp, Bar, Sp, body, CloseBrace);
    private static Formula Part(Formula a) => Call("Subtype", LambdaOf("i", Fin(V("n")),
        new Formula.Relation(V("i"), FormulaRelationOperator.MemberOf, a)));

    private static Formula GhzFormula()
    {
        var condition = Ex("j", Fin(V("d")), All("i", Fin(V("n")), Equal(At(V("x"), V("i")), V("j"))));
        var root = Typed(C("Complex", "ofReal", C("Real", "sqrt", RealD)), Complex);
        var amplitude = Seq(F.Id("if"), Sp, Parenthesized(condition), Sp, F.Id("then"), Sp,
            C("Inv", "inv", root), Sp, F.Id("else"), Sp, Typed(D(0), Complex));
        return ND(Equal(Typed(Call("ghz", V("n"), V("d")), Vector), LambdaOf("x", Word, amplitude)));
    }

    private static Formula BiseparableFormula()
    {
        var a = V("a"); var complement = C("Compl", "compl", a);
        Formula Restrict(Formula part) => LambdaOf("i", Part(part), At(V("x"), C("Subtype", "val", V("i"))));
        var factorization = All("x", Word, Equal(At(V("φ"), V("x")),
            Multiply(At(V("u"), Restrict(a)), At(V("v"), Restrict(complement)))));
        var factors = Ex("u", Arrow(Arrow(Part(a), Fin(V("d"))), Complex),
            Ex("v", Arrow(Arrow(Part(complement), Fin(V("d"))), Complex), factorization));
        var rhs = And(Call("IsUnitState", V("φ")), Ex("a", Call("Finset", Fin(V("n"))),
            And(C("Finset", "Nonempty", a), And(C("Finset", "Nonempty", complement), factors))));
        return ND(All("φ", Vector, IffTo(Call("IsBiseparable", V("φ")), rhs)));
    }

    private static Formula SupportFormula()
    {
        var image = C("Finset", "image", V("x"), Typed(Qualified("Finset", "univ"), Call("Finset", Fin(V("n")))));
        var entry = Seq(F.Id("if"), Sp, Parenthesized(LE(C("Finset", "card", image), Typed(D(2), Nat))),
            Sp, F.Id("then"), Sp, Typed(D(1), Complex), Sp, F.Id("else"), Sp, Typed(D(0), Complex));
        return ND(Equal(Typed(Call("supportProjector", V("n"), V("d")), Matrix),
            C("Matrix", "diagonal", LambdaOf("x", Word, entry))));
    }

    private static Formula WitnessFormula() => ND(Equal(Typed(Call("witnessOp", V("n"), V("d")), Matrix),
        Subtract(Smul(new Formula.Fraction(D(1), RealD), Call("supportProjector", V("n"), V("d"))),
            RankOne(Call("ghz", V("n"), V("d"))))));

    private static Formula NoisyFormula() => WithP(Equal(Typed(Call("noisyGhz", V("n"), V("d"), V("p")), Matrix),
        Add(Smul(new Formula.Fraction(V("p"), new Formula.Power(RealD, V("n"))), Typed(D(1), Matrix)),
            Smul(Subtract(D(1), V("p")), RankOne(Call("ghz", V("n"), V("d")))))));

    private static Formula ValueFormula() => WithP(Equal(Typed(Call("witnessValue", V("n"), V("d"), V("p")), Real),
        C("Complex", "re", C("Matrix", "trace", Multiply(Call("noisyGhz", V("n"), V("d"), V("p")),
            Call("witnessOp", V("n"), V("d")))))));

    private static Formula PureFormula() => ND(All("ψ", Vector,
        Equal(Typed(Call("geometricMeasurePure", V("ψ")), Real), Subtract(D(1), Call("sSup", SetOf("t", Real,
            Ex("φ", Vector, And(Call("IsBiseparable", V("φ")), Equal(V("t"), NormSq(DotOf(V("φ"), V("ψ"))))))))))));

    private static Formula RoofFormula()
    {
        var weight = At(V("p"), V("i")); var state = At(V("ψ"), V("i"));
        var ensemble = Ex("k", Nat, Ex("p", Arrow(Fin(V("k")), Real),
            Ex("ψ", Arrow(Fin(V("k")), Vector),
                And(All("i", Fin(V("k")), LE(D(0), weight)),
                And(Equal(SumOver("i", Fin(V("k")), weight), D(1)),
                And(All("i", Fin(V("k")), Call("IsUnitState", state)),
                And(Equal(V("ρ"), SumOver("i", Fin(V("k")), Smul(weight, RankOne(state)))),
                    Equal(V("t"), SumOver("i", Fin(V("k")), Multiply(weight, Call("geometricMeasurePure", state)))))))))));
        return ND(All("ρ", Matrix, Equal(Typed(Call("geometricMeasure", V("ρ")), Real),
            Call("sInf", SetOf("t", Real, ensemble)))));
    }

    private static Formula HatFormula()
    {
        var value = Subtract(Call("readout", Add(Smul(V("r"), Call("witnessOp", V("n"), V("d"))), RankOne(V("φ"))), V("ψ")), D(1));
        var candidates = Ex("ψ", Vector, Ex("φ", Vector,
            And(Call("IsUnitState", V("ψ")), And(Call("IsBiseparable", V("φ")), Equal(V("t"), value)))));
        return ND(All("r", Real, Equal(Typed(Call("hatE", V("n"), V("d"), V("r")), Real),
            Call("sSup", SetOf("t", Real, candidates)))));
    }

    private static Formula EpsilonFormula() => WithP(Equal(Typed(Call("epsilonO", V("n"), V("d"), V("p")), Real),
        Call("sSup", SetOf("t", Real, Ex("r", Real, Equal(V("t"),
            Subtract(Multiply(V("r"), Call("witnessValue", V("n"), V("d"), V("p"))),
                Call("hatE", V("n"), V("d"), V("r")))))))));

    private static Formula ClaimFormula() => IffTo(Call("claim"), ND(Arrow(LE(D(3), V("n")),
        Arrow(LE(D(3), V("d")), All("p", Real, Arrow(LE(D(0), V("p")), Arrow(LE(V("p"), D(1)),
            Equal(Call("epsilonO", V("n"), V("d"), V("p")),
                Call("geometricMeasure", Call("noisyGhz", V("n"), V("d"), V("p")))))))))));
}
