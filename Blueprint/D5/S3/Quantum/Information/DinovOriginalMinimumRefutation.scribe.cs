using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class DinovOriginalMinimumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dinov2026kime");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At two degrees of freedom, a nonuniform phase density has the same joint action marginal as its uniform-phase product comparator and strictly smaller uncertainty in both degrees of freedom.",
        H("The within-DOF minimum clause of equipartition duality fails"),
        Blocks(
            Paragraph(Text("Real.Angle is the quotient AddCircle(2*pi), with angular volume of mass 2*pi. The action reference measure action is Lebesgue measure restricted to strictly positive reals. TorusOne is Real.Angle times the reals, TorusTwo is its square, and CartesianTwo is the square of a real coordinate pair. torusBase is angular volume times action; torusFullBase is its square. Cartesian volume is the standard product Lebesgue measure. The first Bool index selects the degree of freedom; the second selects q for false and p for true. Pair, fst and snd below denote ordered pairing and projections. integral, integralNN, ae, and withDensity use their indicated measures; ofReal is the nonnegative extended-real embedding. Function spaces and products are ordinary function and Cartesian product types.")),
            Node("PsiA", "The action-angle source map", All("z", V("TorusOne"), Eq(Call("PsiA", V("z")),
                Pair(Mul(Call("sqrt", Mul(D(2), Call("snd", V("z")))), Call("sin", Call("fst", V("z")))),
                     Mul(Call("sqrt", Mul(D(2), Call("snd", V("z")))), Call("cos", Call("fst", V("z"))))))),
                "The sine and cosine are those of the quotient angle. PsiA2 applies PsiA independently to the two coordinate pairs. R2(q,p)=q^2+p^2; radialAction takes R2/2 in each degree of freedom, and actionProjection takes the two action coordinates.", true),
            Node("actualCovariance", "Covariance of the actual Cartesian coordinates", All("mu", Call("Measure", V("CartesianTwo")),
                All("i", Call("Product", V("Bool"), V("Bool")), All("k", Call("Product", V("Bool"), V("Bool")),
                Eq(App(Call("actualCovariance", V("mu")), V("i"), V("k")),
                    Call("covariance", Call("actualCoordinate", V("i")), Call("actualCoordinate", V("k")), V("mu")))))),
                "Covariance is the integral of the centered product under the actual law. No covariance matrix is prescribed as a hypothesis."),
            Node("actualUncertainty", "Within-DOF uncertainty", All("mu", Call("Measure", V("CartesianTwo")),
                All("j", V("Bool"), Eq(Call("actualUncertainty", V("mu"), V("j")),
                    Call("sqrt", Call("det", Call("covarianceBlock", V("mu"), V("j"))))))),
                "covarianceBlock(mu,j) is the two by two q,p principal block of actualCovariance(mu), in that order. The uncertainty is its determinant's nonnegative square root, as in Theorem 3.16.", true),
            Node("cartesianLaw", "The normalized Cartesian density law", All("F", DensityType,
                Eq(Call("cartesianLaw", V("F")), Call("withDensity", V("volume"),
                    Lam("x", Call("ofReal", App(V("F"), V("x"))))))),
                "Normalization and nonnegativity are requirements of sourceState; the density law itself is defined for every real-valued function."),
            Node("sourcePullback", "Density pulled back through the source map", All("F", DensityType,
                All("z", V("TorusTwo"), Eq(Call("sourcePullback", V("F"), V("z")),
                    App(V("F"), Call("PsiA2", V("z")))))),
                "sourceTorusLaw(F) is torusFullBase.withDensity(ofReal(sourcePullback(F))). It uses the actual quotient-angle source map."),
            Node("sourceEntropy", "Cartesian differential entropy", All("F", DensityType,
                Eq(Call("sourceEntropy", V("F")), new Formula.Negate(EntropyIntegral(V("F"), false)))),
                "Entropy uses the natural logarithm. sourceUncertainty(F,j) is actualUncertainty(cartesianLaw(F),j). The finite integrals and the torus-to-Cartesian entropy identity are certified in sourceState."),
            Node("actionDensity", "A joint action density", All("r", ActionDensityType,
                Iff(Call("actionDensity", V("r")), And(Call("Measurable", V("r")),
                    And(All("J", ActionPair, Le(D(0), App(V("r"), V("J")))),
                        Eq(Call("integralNN", ActionMeasure, Lam("J", Call("ofReal", App(V("r"), V("J"))))), D(1)))))),
                "actionLaw(r) is the action product measure weighted by ofReal(r). oneActionDensity is the same measurable, nonnegative, unit-mass condition for one action coordinate."),
            Node("sourceState", "Finite-entropy states with their source realization", StateFormula(),
                "The density is Borel measurable, pointwise nonnegative and normalized on Cartesian volume. Every one of its four Cartesian coordinates belongs to L2, and its full four by four actual covariance is positive definite. Both entropy integrands are integrable; their integrals agree, and PsiA2 pushes the actual source law to the Cartesian density law. These extra certificates restrict the universal comparison and are all established for the counterexample."),
            Node("commonActionMarginal", "The same joint marginal in both representations", MarginalFormula(),
                "For almost every positive action pair J, both angular fibers are integrable and their integrals equal r(J). Both source-law action projections and both Cartesian radial-action projections equal actionLaw(r). Marginal equality is joint equality for the same two actions."),
            Node("phaseUniformProduct", "The phase-uniform product comparator", UniformFormula(),
                "The source density equals r(actionProjection(z))/(2*pi)^2 almost everywhere. The joint action density factors almost everywhere into two actually normalized nonnegative one-action densities. This condition certifies existence of the product comparator."),
            Node("dinovTwoDofMinimumClause", "The necessary two-DOF minimum assertion", ClaimFormula(),
                "Conjecture 3.22 (Equipartition duality): \"Fix n ≥ 2, an entropy value s, and an action marginal ρ_J on (0,∞)^n. Among all states on T^n × (0,∞)^n with entropy ≥ s and action marginal ρ_J, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty u_j, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all j; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup ∂t ρ = Σj (−ωj ∂θj + ε ∂θj²) ρ.\" The formal predicate expresses only a necessary specialization of clause (ii), at n=2, on the certified finite-entropy, L2, positive-definite subclass. The original all-n assertion implies clause (ii), which implies this specialization. The predicate has no n quantifier and makes no separate assertion about clauses (i), (iii), or the semigroup."),
            Node("result", "Both uncertainties are smaller than the comparator's", new Formula.Not(V("dinovTwoDofMinimumClause")),
                "Use r(J1,J2)=exp(-(J1+J2)) and independent phases phi(theta)=(1+cos(2*theta)/2)/(2*pi). Each action has density exp(-J), and the comparator has uniform phases. The two Cartesian densities are the products of the actual one-DOF densities exp(-R2/2)*(1+(p^2-q^2)/(2*R2))/(2*pi) and exp(-R2/2)/(2*pi); the first is set to zero at R2=0. The zero-action planes have zero measure. Change of variables proves normalization, the source pushforwards, common joint marginal and entropy equality. Both entropies are finite and nonnegative, so s=0 is admissible. The actual covariance matrices, ordered q1,p1,q2,p2, are diag(3/4,5/4,3/4,5/4) and the identity. Both are positive definite and all coordinates belong to L2. For each of the two degrees of freedom the uncertainties are sqrt(15/16) and 1, respectively, with sqrt(15/16)<1. Adding both strict comparisons contradicts the sum of both inequalities required by the minimum assertion. Thus clause (ii), and hence the simultaneous conjecture as written, fails. Entropy maximization, saturation uniqueness and semigroup claims receive no separate settlement here.",
                role: DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dinov-2026-equipartition-duality-minimum-refutation"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, bool literature = false, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("dinov-minimum-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Lam(string name, Formula body) => Seq(Named("fun"), Sp, V(name), Sp, Mapsto, Sp, Grp(body));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Grp(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Grp(a), b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula DensityType => new Formula.TypeArrow(V("CartesianTwo"), R);
    private static Formula ActionPair => Call("Product", R, R);
    private static Formula ActionDensityType => new Formula.TypeArrow(ActionPair, R);
    private static Formula OneActionDensityType => new Formula.TypeArrow(R, R);
    private static Formula ActionMeasure => Call("prod", V("action"), V("action"));
    private static Formula Law(Formula f) => Call("cartesianLaw", f);
    private static Formula TorusLaw(Formula f) => Call("sourceTorusLaw", f);
    private static Formula EntropyFunction(Formula f, bool torus) => Lam("x", Mul(
        torus ? Call("sourcePullback", f, V("x")) : App(f, V("x")),
        Call("log", torus ? Call("sourcePullback", f, V("x")) : App(f, V("x")))));
    private static Formula EntropyIntegral(Formula f, bool torus) =>
        Call("integral", torus ? V("torusFullBase") : V("volume"), EntropyFunction(f, torus));

    private static Formula StateFormula()
    {
        var f = V("F");
        return All("F", DensityType, Iff(Call("sourceState", f),
            And(Call("Measurable", f), And(All("x", V("CartesianTwo"), Le(D(0), App(f, V("x")))),
            And(Call("IsProbabilityMeasure", Law(f)), And(Call("Integrable", EntropyFunction(f, false), V("volume")),
            And(All("i", Call("Product", V("Bool"), V("Bool")), Call("MemLp", Call("actualCoordinate", V("i")), D(2), Law(f))),
            And(Call("PosDef", Call("actualCovariance", Law(f))),
            And(Call("Integrable", EntropyFunction(f, true), V("torusFullBase")),
            And(Eq(EntropyIntegral(f, true), EntropyIntegral(f, false)),
                Eq(Call("map", V("PsiA2"), TorusLaw(f)), Law(f))))))))))));
    }

    private static Formula Fiber(Formula f) => Lam("ts", Call("sourcePullback", f,
        Pair(Pair(Call("fst", V("ts")), Call("fst", V("J"))), Pair(Call("snd", V("ts")), Call("snd", V("J"))))));
    private static Formula Fibers(Formula f) => Call("ae", ActionMeasure, Lam("J",
        And(Call("Integrable", Fiber(f), V("volume")), Eq(Call("integral", V("volume"), Fiber(f)), App(V("r"), V("J"))))));
    private static Formula ActionMap(Formula f, bool torus) => Eq(
        Call("map", V(torus ? "actionProjection" : "radialAction"), torus ? TorusLaw(f) : Law(f)), Call("actionLaw", V("r")));
    private static Formula MarginalFormula() => All("F", DensityType, All("G", DensityType, All("r", ActionDensityType,
        Iff(Call("commonActionMarginal", V("F"), V("G"), V("r")), And(Fibers(V("F")), And(Fibers(V("G")),
            And(ActionMap(V("F"), true), And(ActionMap(V("G"), true), And(ActionMap(V("F"), false), ActionMap(V("G"), false))))))))));
    private static Formula UniformFormula() => All("G", DensityType, All("r", ActionDensityType,
        Iff(Call("phaseUniformProduct", V("G"), V("r")), And(
            Call("aeEq", V("torusFullBase"), Call("sourcePullback", V("G")), Lam("z",
                new Formula.Fraction(App(V("r"), Call("actionProjection", V("z"))), Pow(Mul(D(2), Pi), D(2))))),
            Exists("rone", OneActionDensityType, Exists("rtwo", OneActionDensityType,
                And(Call("oneActionDensity", V("rone")), And(Call("oneActionDensity", V("rtwo")),
                    Call("aeEq", ActionMeasure, V("r"), Lam("J", Mul(App(V("rone"), Call("fst", V("J"))), App(V("rtwo"), Call("snd", V("J"))))))))))))));
    private static Formula ClaimFormula() => Iff(V("dinovTwoDofMinimumClause"), All("s", R, All("r", ActionDensityType,
        All("F", DensityType, All("G", DensityType,
            Imp(Call("actionDensity", V("r")), Imp(Call("sourceState", V("F")), Imp(Call("sourceState", V("G")),
            Imp(Call("commonActionMarginal", V("F"), V("G"), V("r")), Imp(Call("phaseUniformProduct", V("G"), V("r")),
            Imp(Le(V("s"), Call("sourceEntropy", V("F"))), Imp(Le(V("s"), Call("sourceEntropy", V("G"))),
                All("j", V("Bool"), Le(Call("sourceUncertainty", V("G"), V("j")), Call("sourceUncertainty", V("F"), V("j"))))))))))))))));
}
