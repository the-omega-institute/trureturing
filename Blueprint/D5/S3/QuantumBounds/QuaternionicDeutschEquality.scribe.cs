using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class QuaternionicDeutschEqualityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/QuaternionicDeutschEquality.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/krishna2026quaternionicdeutsch");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lower Deutsch equality for quaternionic continuous Parseval frames is equivalent to rank-one rigidity and implies simultaneous equality.",
        H("Quaternionic Deutsch equality"),
        Blocks(
            Node("RightHilbert", "Right quaternionic inner product", RightHilbertFormula(),
                "Definition 1.9, printed pages 4–5: “A right quaternionic vector space 𝒬 over ℍ is said to be a (right) quaternionic Hilbert space if there exists a map (called as quaternionic inner product) ⟨·, ·⟩: 𝒬 × 𝒬 → ℍ such that the following hold.” The record gives all inner-product fields; completeness is a separate CompleteSpace hypothesis in the classification. Right scalar multiplication by q is (MulOpposite.op q) • x. The displayed record lists its inner map and all seven laws.", AssessedProvenance.FromLiterature(Source)),
            Node("ContinuousParseval", "Continuous Parseval frame", ContinuousParsevalFormula(),
                "Definition 2.7, printed page 10: “Let (Ω, μ) be a measure space. A collection {τα}α∈Ω in a quaternionic Hilbert space 𝒬 is said to be a continuous Parseval frame for 𝒬 if the following conditions hold.” “For each x ∈ 𝒬, the map Ω ∋ α ↦ ⟨τα, x⟩ ∈ ℍ is measurable.” Its second condition is ‖x‖² = ∫Ω |⟨τα, x⟩|² dμ(α) for every x. Quaternionic coefficients use the Borel measurable space. The nonnegative extended integral retains divergent values.", AssessedProvenance.FromLiterature(Source)),
            Node("OneBounded", "Pointwise norm bound", OneBoundedFormula(),
                "Definition 2.8, printed page 10: “A continuous Parseval frame {τα}α∈Ω for 𝒬 is said to be 1-bounded if” ‖τα‖ ≤ 1, ∀ α ∈ Ω. This includes indices of measure zero.", AssessedProvenance.FromLiterature(Source)),
            Node("EntropyDomain", "Everywhere nonzero coefficients", EntropyDomainFormula(),
                "Printed page 10: 𝒬τ ≔ {x ∈ 𝒬: ⟨τα, x⟩ ≠ 0, ∀ α ∈ Ω}. Membership requires a nonzero coefficient at every index.", AssessedProvenance.FromLiterature(Source)),
            Node("unitVector", "Right normalization", UnitVectorFormula(),
                "Section 2, printed page 5, states: “by x/r, we mean x r⁻¹.” Here r is the nonzero real norm of the state; its inverse is coerced to Quaternion ℝ before MulOpposite.op acts on the vector.", AssessedProvenance.FromLiterature(Source)),
            Node("density", "Squared normalized coefficient", DensityFormula(),
                "The coefficient density appearing in the continuous Shannon formula is the squared norm of the quaternionic inner product with the normalized state.", AssessedProvenance.FromLiterature(Source)),
            Node("entropy", "Continuous Shannon entropy", EntropyFormula(),
                "Printed page 10: “Given a continuous 1-bounded Parseval frame {τα}α∈Ω for 𝒬, we define the continuous Shannon entropy at a point x ∈ 𝒬τ as” Sτ(x) ≔ −∫Ω |⟨τα, x/‖x‖⟩|² log |⟨τα, x/‖x‖⟩|² dμ(α) ≥ 0. The natural logarithm and the extended nonnegative integral retain possible infinite entropy.", AssessedProvenance.FromLiterature(Source)),
            Node("overlap", "Pointwise cross supremum", OverlapFormula(),
                "The supremum in Theorem 2.9, equation (11), printed page 11, ranges over every pair of indices. It is the actual real supremum rather than an essential supremum.", AssessedProvenance.FromLiterature(Source)),
            Node("deutschEndpoint", "Deutsch lower endpoint", DeutschEndpointFormula(),
                "The central lower endpoint in equation (11), printed page 11, is minus twice the natural logarithm of (1 + overlap)/2, embedded into ENNReal.", AssessedProvenance.FromLiterature(Source)),
            Node("lowerEquality", "Equality at the lower endpoint", LowerEqualityFormula(),
                "The sum of the two entropies equals the central Deutsch endpoint from equation (11).", AssessedProvenance.FromRepo(Source)),
            Node("rigid", "Rank-one rigidity", RigidFormula(),
                "The space has quaternionic rank one, and both frame families have unit norm almost everywhere with respect to their own measures.", AssessedProvenance.FromRepo(Source)),
            Node("simultaneousEquality", "Simultaneous equality", SimultaneousFormula(),
                "Both total masses and the pointwise overlap equal one, and both entropies vanish. Thus every endpoint of equation (11) equals zero.", AssessedProvenance.FromRepo(Source)),
            Node("equalityModelExists", "A nonvacuous equality model", EqualityModelFormula(),
                "There exist a complete right quaternionic space, two continuous Parseval frames of norm at most one, and a nonzero state with everywhere nonzero coefficients and lower equality. The proof constructs the ULift quaternionic line and singleton Dirac index spaces at arbitrary universes.", AssessedProvenance.FromRepo(Source)),
            Node("claim", "Question 2.12 and the classification", Equal(Named("claim"), Parenthesized(ClaimBody())),
                "Question 2.12, printed page 12, asks verbatim: “Let (Ω, μ), (Δ, ν) be measure spaces, 𝒬 be a quaternionic Hilbert space. For which pairs of 1-bounded continuous Parseval frames {τα}α∈Ω and {ωβ}β∈Δ for 𝒬, we have equality in Inequality (11)?” Q is a right module over MulOpposite (Quaternion ℝ), h is its inner-product record, and the two index spaces have arbitrary measures. The answer classifies the central lower equality for each nonzero state in both entropy domains and then classifies existence of such a state for the pair. Completeness is retained. The upper link alone is outside this statement.", AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + "result"),
                H("Lower equality is rigid and simultaneous"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Quaternionic Buzano bounds the product of the two coefficient densities. Actual bounded suprema give entropy decompositions with nonnegative remainder integrals. Equality makes both densities constant almost everywhere. Parseval at saturated frame vectors identifies both constants as the squared overlap; the scalar identity forces overlap one. Parseval applied to an orthogonal residual then forces rank one. Conversely, rank one and unit frame norms almost everywhere give both masses one and both entropies zero. Pair existence also requires every frame vector to be nonzero, including null indices. No product-measure sigma-finiteness assumption or finite total mass is imposed."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("quaternionic-deutsch"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Module + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula ExistsInstance(Formula type, Formula body) => Seq(Exists, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, body);
    private static Formula And(params Formula[] values)
    {
        var body = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            body = new Formula.Logic(Parenthesized(values[i]), FormulaLogicOperator.And, Parenthesized(body));
        return body;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula LeOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Pow(Formula a) => new Formula.Power(Parenthesized(a), D(2));
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Quaternions => Call("Quaternion", Reals);
    private static Formula Opposite => Call("MulOpposite", Quaternions);
    private static Formula Q => X("Q");
    private static Formula OmegaType => X("Omega");
    private static Formula DeltaType => X("Delta");
    private static Formula Inner(Formula a, Formula b) => At(Qualified("RightHilbert", "inner"), X("h"), a, b);
    private static Formula Frame(string name, string index) => At(X(name), X(index));
    private static Formula ScalarAction(Formula q, Formula x) => At(Qualified("HSMul", "hSMul"), At(Qualified("MulOpposite", "op"), q), x);
    private static Formula Coerce(Formula x, Formula type) => Typed(x, type);
    private static Formula OfReal(Formula x) => At(Qualified("ENNReal", "ofReal"), x);
    private static Formula Integral(string index, Formula indexType, Formula measure, Formula body) =>
        At(Qualified("MeasureTheory", "lintegral"), measure, Lam(index, indexType, body));
    private static Formula Ae(string index, Formula indexType, Formula measure, Formula body) =>
        At(Qualified("Filter", "Eventually"), Lam(index, indexType, body), At(Qualified("MeasureTheory", "ae"), measure));
    private static Formula Entropy(string measure, string frame) => Call("entropy", X("h"), X(measure), X(frame), X("x"));
    private static Formula Lower => Call("lowerEquality", X("h"), X("mu"), X("nu"), X("tau"), X("omega"), X("x"));
    private static Formula Rigid => Call("rigid", X("mu"), X("nu"), X("tau"), X("omega"));
    private static Formula Simultaneous => Call("simultaneousEquality", X("h"), X("mu"), X("nu"), X("tau"), X("omega"), X("x"));
    private static Formula InDomain(string frame) => Member(X("x"), Call("EntropyDomain", X("h"), X(frame)));
    private static Formula Overlap => Call("overlap", X("h"), X("tau"), X("omega"));
    private static Formula Mass(string measure) => At(X(measure), Qualified("Set", "univ"));
    private static Formula Space(Formula body, bool module = true) => All("Q", X("Type"),
        Instance(Call("NormedAddCommGroup", Q), module ? Instance(Call("Module", Opposite, Q), body) : body));
    private static Formula Indices(Formula body, bool pair, bool measurable)
    {
        if (pair)
            body = All("Delta", X("Type"), measurable ? Instance(Call("MeasurableSpace", DeltaType), body) : body);
        return All("Omega", X("Type"), measurable ? Instance(Call("MeasurableSpace", OmegaType), body) : body);
    }
    private static Formula FrameParameters(Formula body, bool pair, bool measures, bool state, bool inner = true)
    {
        if (state) body = All("x", Q, body);
        if (pair) body = All("omega", Arrow(DeltaType, Q), body);
        body = All("tau", Arrow(OmegaType, Q), body);
        if (measures)
        {
            if (pair) body = All("nu", At(Qualified("MeasureTheory", "Measure"), DeltaType), body);
            body = All("mu", At(Qualified("MeasureTheory", "Measure"), OmegaType), body);
        }
        return inner ? All("h", Call("RightHilbert", Q), body) : body;
    }

    private static Formula RightHilbertFormula()
    {
        Formula Map(Formula a, Formula b) => At(X("inner"), a, b);
        var laws = And(
            All("x", Q, Equal(Map(X("x"), X("x")), Coerce(At(Qualified("Quaternion", "re"), Map(X("x"), X("x"))), Quaternions))),
            All("x", Q, LeOf(D(0), At(Qualified("Quaternion", "re"), Map(X("x"), X("x"))))),
            All("x", Q, Imp(Equal(Map(X("x"), X("x")), D(0)), Equal(X("x"), D(0)))),
            All("x", Q, All("y", Q, All("z", Q, Equal(Map(Add(X("x"), X("y")), X("z")), Add(Map(X("x"), X("z")), Map(X("y"), X("z"))))))),
            All("x", Q, All("y", Q, All("q", Quaternions, Equal(Map(X("x"), ScalarAction(X("q"), X("y"))), Multiply(Map(X("x"), X("y")), X("q")))))),
            All("x", Q, All("y", Q, Equal(Map(X("x"), X("y")), Call("star", Map(X("y"), X("x")))))),
            All("x", Q, Equal(Norm(X("x")), At(Qualified("Real", "sqrt"), At(Qualified("Quaternion", "re"), Map(X("x"), X("x")))))));
        return Space(Seq(Call("RightHilbert", Q), Sp, Colon, Eq, Sp, OpenBrace,
            Seq(X("inner"), Sp, Colon, Sp, Arrow(Q, Arrow(Q, Quaternions))), Semi, Sp,
            laws, CloseBrace));
    }

    private static Formula ContinuousParsevalFormula()
    {
        var coefficient = Inner(Frame("tau", "alpha"), X("x"));
        var body = And(All("x", Q,
            At(Named("Measurable"), Lam("alpha", OmegaType, coefficient))),
            All("x", Q, Equal(Integral("alpha", OmegaType, X("mu"), OfReal(Pow(Norm(coefficient)))), OfReal(Pow(Norm(X("x")))))));
        return Space(Indices(FrameParameters(Equal(Call("ContinuousParseval", X("h"), X("mu"), X("tau")), Parenthesized(body)), false, true, false), false, true));
    }
    private static Formula OneBoundedFormula() => Space(Indices(FrameParameters(
        Equal(Call("OneBounded", X("tau")), Parenthesized(All("alpha", OmegaType, LeOf(Norm(Frame("tau", "alpha")), D(1))))),
        false, false, false, false), false, false), false);
    private static Formula EntropyDomainFormula() => Space(Indices(FrameParameters(
        Equal(Call("EntropyDomain", X("h"), X("tau")),
            At(Named("setOf"), Lam("x", Q, All("alpha", OmegaType, Ne(Inner(Frame("tau", "alpha"), X("x")), D(0)))))),
        false, false, false), false, false));
    private static Formula UnitVectorFormula() => Space(All("x", Q,
        Equal(Call("unitVector", X("x")), ScalarAction(Coerce(new Formula.Power(Parenthesized(Norm(X("x"))), Negate(D(1))), Quaternions), X("x")))));
    private static Formula DensityFormula() => Space(Indices(FrameParameters(All("alpha", OmegaType,
        Equal(Call("density", X("h"), X("tau"), X("x"), X("alpha")), Pow(Norm(Inner(Frame("tau", "alpha"), Call("unitVector", X("x"))))))),
        false, false, true), false, false));
    private static Formula EntropyFormula()
    {
        var density = Call("density", X("h"), X("tau"), X("x"), X("alpha"));
        var integrand = OfReal(Multiply(Negate(density), At(Qualified("Real", "log"), density)));
        var body = Equal(Call("entropy", X("h"), X("mu"), X("tau"), X("x")),
            Integral("alpha", OmegaType, X("mu"), integrand));
        return Space(Indices(FrameParameters(body, false, true, true), false, true));
    }
    private static Formula OverlapFormula() => Space(Indices(FrameParameters(
        Equal(Overlap, Call("sSup", At(Qualified("Set", "range"), Lam("z", Call("Prod", OmegaType, DeltaType),
            Norm(Inner(At(X("tau"), At(Qualified("Prod", "fst"), X("z"))), At(X("omega"), At(Qualified("Prod", "snd"), X("z"))))))))),
        true, false, false), true, false));
    private static Formula DeutschEndpointFormula() => Space(Indices(FrameParameters(
        Equal(Call("deutschEndpoint", X("h"), X("tau"), X("omega")),
            OfReal(Multiply(Negate(D(2)), At(Qualified("Real", "log"), new Formula.Fraction(Add(D(1), Overlap), D(2)))))),
        true, false, false), true, false));
    private static Formula LowerEqualityFormula() => Space(Indices(FrameParameters(
        Equal(Lower, Parenthesized(Equal(Add(Entropy("mu", "tau"), Entropy("nu", "omega")), Call("deutschEndpoint", X("h"), X("tau"), X("omega"))))),
        true, true, true), true, true));
    private static Formula RigidFormula() => Space(Indices(FrameParameters(Equal(Rigid, Parenthesized(And(
        Equal(At(Qualified("Module", "rank"), Opposite, Q), D(1)),
        Ae("alpha", OmegaType, X("mu"), Equal(Norm(Frame("tau", "alpha")), D(1))),
        Ae("beta", DeltaType, X("nu"), Equal(Norm(Frame("omega", "beta")), D(1)))))),
        true, true, false, false), true, true));
    private static Formula SimultaneousFormula() => Space(Indices(FrameParameters(Equal(Simultaneous, Parenthesized(And(
        Equal(Mass("mu"), D(1)), Equal(Mass("nu"), D(1)), Equal(Overlap, D(1)),
        Equal(Entropy("mu", "tau"), D(0)), Equal(Entropy("nu", "omega"), D(0))))),
        true, true, true), true, true));

    private static Formula EqualityModelBody()
    {
        var body = And(Call("ContinuousParseval", X("h"), X("mu"), X("tau")),
            Call("ContinuousParseval", X("h"), X("nu"), X("omega")), Call("OneBounded", X("tau")), Call("OneBounded", X("omega")),
            Ne(X("x"), D(0)), InDomain("tau"), InDomain("omega"), Lower);
        body = Some("mu", At(Qualified("MeasureTheory", "Measure"), OmegaType),
            Some("nu", At(Qualified("MeasureTheory", "Measure"), DeltaType),
            Some("tau", Arrow(OmegaType, Q), Some("omega", Arrow(DeltaType, Q), Some("x", Q, body)))));
        body = ExistsInstance(Call("MeasurableSpace", OmegaType), ExistsInstance(Call("MeasurableSpace", DeltaType), body));
        body = Some("h", Call("RightHilbert", Q), Some("Omega", X("Type"), Some("Delta", X("Type"), body)));
        return Some("Q", X("Type"), ExistsInstance(Call("NormedAddCommGroup", Q),
            ExistsInstance(Call("Module", Opposite, Q), ExistsInstance(Call("CompleteSpace", Q), body))));
    }
    private static Formula EqualityModelFormula() => Equal(Named("equalityModelExists"), Parenthesized(EqualityModelBody()));
    private static Formula ClaimBody()
    {
        var state = All("x", Q, Imp(Ne(X("x"), D(0)), Imp(InDomain("tau"), Imp(InDomain("omega"),
            And(IffOf(Lower, Rigid), Imp(Lower, Simultaneous))))));
        var existence = IffOf(Some("x", Q, And(Ne(X("x"), D(0)), InDomain("tau"), InDomain("omega"), Lower)),
            And(Rigid, All("alpha", OmegaType, Ne(Frame("tau", "alpha"), D(0))), All("beta", DeltaType, Ne(Frame("omega", "beta"), D(0)))));
        var body = Imp(Call("ContinuousParseval", X("h"), X("mu"), X("tau")),
            Imp(Call("ContinuousParseval", X("h"), X("nu"), X("omega")),
            Imp(Call("OneBounded", X("tau")), Imp(Call("OneBounded", X("omega")), And(state, existence)))));
        body = All("mu", At(Qualified("MeasureTheory", "Measure"), OmegaType),
            All("nu", At(Qualified("MeasureTheory", "Measure"), DeltaType),
            All("tau", Arrow(OmegaType, Q), All("omega", Arrow(DeltaType, Q), body))));
        body = Instance(Call("MeasurableSpace", OmegaType), Instance(Call("MeasurableSpace", DeltaType), body));
        body = All("h", Call("RightHilbert", Q), All("Omega", X("Type"), All("Delta", X("Type"), body)));
        return And(Named("equalityModelExists"), Space(Instance(Call("CompleteSpace", Q), body)));
    }
}
