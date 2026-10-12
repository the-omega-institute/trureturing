using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class InteractionPictureAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ContinuousObservables/madouremizovvafadar2024semigroups");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite past interaction integrals do not imply polynomial-generator asymptotics.",
        H("A counterexample to interaction-picture asymptotics"),
        Blocks(
            SourceQuotation(),
            Entry("matrix-space", "M3", "Complex three-dimensional matrices",
                Disp(Eqn(V("M3"), Call("Matrix", Call("Fin", D(3)), Call("Fin", D(3)), Complex))),
                "M3 is the space of complex 3×3 matrices. In the error estimate it carries the entrywise "
                + "sup norm. The Banach space in the source correspondence is B=ℂ³ with its sup norm; "
                + "matrices act as bounded operators. Matrix exponentials are independent of the choice "
                + "of equivalent norm in finite dimension.", DescribeRole.Definition, false),
            Entry("coupling", "coupling", "Interaction-picture coupling", Coupling(),
                "coupling D N s is exp(−sD) N exp(sD), for real s and complex matrices D,N. "
                + "The source parameters are L₀=D and L=N. The real scalars are embedded in ℂ before "
                + "matrix scalar multiplication. Bounded generators D+λN define C₀-semigroups for every "
                + "real λ, and exp(sD) is a group with inverse exp(−sD).",
                DescribeRole.Definition, true),
            Entry("hypotheses", "Hyp", "Past-integrability hypotheses at order one", Hypotheses(),
                "Hyp P D N requires P²=P, DP=PD, and PNP=0. Commutation implies that the free evolution "
                + "preserves both PB and (I−P)B. It also requires Lebesgue integrability of the first "
                + "projected interaction, of each second inner integrand, and of the resulting inner "
                + "integral, on the indicated past intervals. Every endpoint t is real, including "
                + "negative endpoints, so this is stronger than requiring only t≥0. In the formula, "
                + "pastIntegral(a,f) means the Lebesgue integral of f over (−∞,a], and IntegrableOn(f,Iic(a)) "
                + "is Lebesgue integrability on that interval. These stronger integrability conditions imply the finite-integral hypotheses of the source for n=1.",
                DescribeRole.Definition, true),
            Entry("expansion", "Expansion", "Polynomial preparation and generator", ExpansionStatement(),
                "Expansion P D N allows arbitrary m∈ℕ and R,G : Fin m → M3. The notation poly(A,λ) "
                + "means ∑_{j∈Fin m} λʲ Aⱼ, with j interpreted as its natural value and λ embedded in ℂ. "
                + "Each fixed t>0 has its own real C and δ>0; there is no uniformity in t and no separate "
                + "positivity condition on C. The error norm is the entrywise sup norm and the error order "
                + "is λ⁴, corresponding to n=1. Different degrees can be padded with zero coefficients. "
                + "The coefficients need not be supported on PB. Thus the permitted approximants include "
                + "all source approximants: for G=PGP and R=PRP, exp(tG)R is the embedded semigroup on PB "
                + "times its preparation. This embedding correspondence is mathematical reasoning.",
                DescribeRole.Definition, false),
            Entry("claim", "claim", "The order-one implication", Claim(),
                "The claim states that every triple P,D,N of complex 3×3 matrices satisfying Hyp "
                + "admits Expansion. The dimension is fixed at three and n=1; a counterexample suffices "
                + "to refute the first question of Problem 29. The projection in the instance has rank two.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "Past integrability does not ensure the expansion",
                Disp(Seq(Neg, Sp, V("claim"))),
                "Take P=diag(1,0,1), D=diag(−3,−2,−1), N=E₁₂+E₂₃, and E=N²=E₁₃, "
                + "with one-based matrix coordinates. projection_algebra proves P²=P, DP=PD, PNP=0. "
                + "coupling_formula gives Lₛ=eˢN. first_integrand is zero, second_integrand is "
                + "e^(s₁+s₂)E, and inner_integral is e^(2s₁)E. hypotheses proves their required "
                + "integrability for every real endpoint. The outer integral is e^(2t)E/2 by exact "
                + "integration. The full identity exp(−sD)exp(s(D+λN))=I+λ(eˢ−1)N+λ²(eˢ−1)²E/2 "
                + "is exact mathematical reasoning; projected_entry proves its projected (1,3) entry. "
                + "At s=t/λ² this entry is λ²(e^(t/λ²)−1)²/2≥t²/(2λ²) for t,λ>0. "
                + "The lemma growth uses t=1 and the fact that an entry norm is at most the matrix norm. "
                + "polynomial_continuous and locally_bounded show that exp(G(λ))R(λ) is bounded near zero. "
                + "no_expansion contradicts the order-four error at t=1, and result proves ¬ claim. "
                + "The finite-dimensional generator and subspace correspondences give a negative answer "
                + "to the first question of Problem 29. By mathematical reasoning, N³=0 makes all products "
                + "of three or more interactions vanish, so the same instance meets the hypotheses for "
                + "n≥2; the higher-order estimate would imply the refuted order-four estimate. This "
                + "extension is not formalized in the module. The mechanism is exponential contraction "
                + "of the free evolution and amplification by its inverse: fixed-endpoint past "
                + "integrability does not control endpoints t/λ² tending to infinity. Isometric free "
                + "evolution on (I−P)B, or a uniform bound there on both the free evolution and its inverse, "
                + "would exclude this example. Whether these candidate restrictions suffice, and the "
                + "second question of Problem 29, are not settled by this result. The relation to "
                + "Teretenkov arXiv:2008.02820 and Davies' weak-coupling literature is limited to titles "
                + "and abstracts; their detailed hypotheses and applicability are ASSUMED-UNVERIFIED. "
                + "No literature priority is established.", DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "F. Madou, I. Remizov, M. Vafadar (eds.), Open problems in one-parameter operator semigroups theory, "
        + "arXiv:2410.00416v2, p. 21, Problem 29 (A. E. Teretenkov), verbatim: “"
        + "Problem 29 (A.E. Teretenkov). Let B be a Banach space. Let P be a projection on a finite-dimensional "
        + "Banach subspace of B. Let L0 + λL be a generator of C0-semigroup U^λ_t on B for all λ ∈ [0, λsup). "
        + "Let U^0_t leave both PB and its complement (I − P)B invariant, let PLP = 0. Denote L_t ≡ "
        + "(U^0_t)^{−1} L U^0_t. Let the integrals ∫_{−∞}^{t} dt_1 … ∫_{−∞}^{t_{k−1}} dt_k "
        + "P L_{t_1} … L_{t_k} P, k = 1, …, n + 1 be finite for all t ⩾ 0. If is it possible to find "
        + "such a λ-dependent operator r^{n,λ} on PB, which is polynomial in λ, and λ-dependent semigroup "
        + "u^{n,λ}_t on PB, whose generator is polynomial in λ, such that P(U^0_{t/λ²})^{−1} U^λ_{t/λ²} P "
        + "= u^{n,λ}_t r^{n,λ} + O(λ^{2n+2}), λ → +0 for all t > 0 ? Let us emphasize that we do not "
        + "assume here asymptotic behaviour to be uniform in t, it is just assumed for each fixed t > 0. "
        + "If there are counterexamples, what further restrictions should be assumed to obtain such an "
        + "asymptotic estimate?”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("teretenkov-2024-interaction-picture-asymptotics"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => V("M3");
    private static Formula Coefficients => Seq(Call("Fin", V("m")), Sp, To, Sp, Mat);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalent(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, byte exponent) => new Formula.Power(a, D(exponent));
    private static Formula Scale(Formula a, Formula b) => Call("smul", Call("ofReal", a), b);
    private static Formula Fn(string name, Formula body) =>
        Parenthesized(Seq(V(name), Sp, Mapsto, Sp, body));
    private static Formula Integrable(Formula f, Formula endpoint) =>
        Call("IntegrableOn", f, Call("Iic", endpoint));
    private static Formula Interaction(Formula s) => Call("coupling", V("D"), V("N"), s);
    private static Formula First(Formula s) => Mul(Mul(V("P"), Interaction(s)), V("P"));
    private static Formula Second(Formula s, Formula u) =>
        Mul(Mul(Mul(V("P"), Interaction(s)), Interaction(u)), V("P"));
    private static Formula Parameters(Formula body) =>
        All("P", Mat, All("D", Mat, All("N", Mat, body)));

    private static Formula Coupling() => Disp(All("D", Mat, All("N", Mat, All("s", Real,
        Eqn(Interaction(V("s")), Mul(Mul(Call("exp", Scale(new Formula.Negate(V("s")), V("D"))),
            V("N")), Call("exp", Scale(V("s"), V("D")))))))));

    private static Formula Hypotheses()
    {
        Formula algebra = And(Eqn(Mul(V("P"), V("P")), V("P")),
            And(Eqn(Mul(V("D"), V("P")), Mul(V("P"), V("D"))),
                Eqn(Mul(Mul(V("P"), V("N")), V("P")), D(0))));
        Formula first = All("t", Real, Integrable(Fn("s", First(V("s"))), V("t")));
        Formula inner = All("s1", Real,
            Integrable(Fn("s2", Second(V("s1"), V("s2"))), V("s1")));
        Formula outer = Integrable(Fn("s1",
            Call("pastIntegral", V("s1"), Fn("s2", Second(V("s1"), V("s2"))))), V("t"));
        Formula second = All("t", Real, And(inner, outer));
        return Disp(Parameters(Equivalent(Call("Hyp", V("P"), V("D"), V("N")),
            And(algebra, And(first, second)))));
    }

    private static Formula ExpansionStatement()
    {
        Formula time = new Formula.Fraction(V("t"), Pow(V("l"), 2));
        Formula perturbed = Add(V("D"), Scale(V("l"), V("N")));
        Formula target = Mul(Mul(Mul(V("P"),
            Call("exp", Scale(new Formula.Negate(time), V("D")))),
            Call("exp", Scale(time, Parenthesized(perturbed)))), V("P"));
        Formula approximant = Mul(Call("exp", Scale(V("t"), Call("poly", V("G"), V("l")))),
            Call("poly", V("R"), V("l")));
        Formula error = AtMost(Call("norm", Parenthesized(Sub(target, approximant))),
            Mul(V("C"), Pow(V("l"), 4)));
        Formula bound = All("l", Real, Imp(Less(D(0), V("l")), Imp(Less(V("l"), V("delta")), error)));
        Formula constants = Ex("C", Real, Ex("delta", Real, And(Less(D(0), V("delta")), bound)));
        Formula times = All("t", Real, Imp(Less(D(0), V("t")), constants));
        Formula coefficients = Ex("m", Nat, Ex("R", Coefficients, Ex("G", Coefficients, times)));
        return Disp(Parameters(Equivalent(Call("Expansion", V("P"), V("D"), V("N")), coefficients)));
    }

    private static Formula Claim() => Disp(Equivalent(V("claim"), Parameters(
        Imp(Call("Hyp", V("P"), V("D"), V("N")),
            Call("Expansion", V("P"), V("D"), V("N"))))));
}
