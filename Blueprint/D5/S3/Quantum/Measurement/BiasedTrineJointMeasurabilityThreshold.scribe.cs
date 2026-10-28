using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class BiasedTrineJointMeasurabilityThresholdDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/yadavalliandrejickunjwal2024qualitative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The biased trine qubit family has triplewise joint-measurability threshold min(2/3, 1 - |b|).",
        H("The exact compatibility threshold for biased trine qubit measurements"),
        Blocks(
            Definition("trine-dir", "trineDir", "The three trine directions", TrineDirFormula(),
                "The three unit vectors lie in the xz plane at angles 2π/3, 4π/3 and 2π. "
                    + "The index i in Fin 3 corresponds to the source's index i + 1. "
                    + "Their coordinates are ordered x, y, z, and WithLp.toLp equips the coordinate "
                    + "functions with the Euclidean norm. These are the directions in Supplemental "
                    + "Material TeX lines 117–118; their explicit coordinates also fix the index order."),
            Definition("trine-effect", "trineEffect", "The common-bias binary effects", TrineEffectFormula(),
                "For bias b and purity η, each direction k gives two complex two-by-two matrices. "
                    + "The parameter eta in the formulas denotes η. The real sign sgn x is +1 for "
                    + "true and −1 for false. The function scalarB(t,a) is t times the identity plus "
                    + "the Pauli matrix expansion of a, so the displayed expression is precisely the "
                    + "first family in Supplemental Material TeX line 115. The outer scalar one half "
                    + "belongs to the complex numbers; the bias and Bloch-vector coefficients are real. "
                    + "On the domain −1 ≤ b ≤ 1, 0 ≤ η ≤ 1 and |b| ≤ 1 − η, these are binary POVMs."),
            Definition("triplewise-jointly-measurable", "TriplewiseJointlyMeasurable",
                "A common eight-outcome measurement", JointMeasurabilityFormula(),
                "Triplewise joint measurability means that one POVM indexed by the eight functions "
                    + "Fin 3 → Bool has each of the three binary measurements as a marginal. Thus its "
                    + "matrices G(s) are positive semidefinite, sum to the identity, and satisfy "
                    + "∑ over s with s(k) = x of G(s) = trineEffect(b,η,k,x) for every k and x. "
                    + "This is the existence condition for the triplewise joint POVM in Supplemental "
                    + "Material TeX lines 131 and 147–150."),
            Definition("trine-threshold", "trineThreshold", "The piecewise threshold", ThresholdFormula(),
                "The function is 1 + b below −1/3, is 2/3 throughout the closed interval "
                    + "[−1/3,1/3], and is 1 − b above 1/3. These are the three expressions in "
                    + "Supplemental Material TeX lines 151–158. The definition gives a real value "
                    + "for every real b; the compatibility theorem concerns the stated physical domain."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The exact triplewise joint-measurability criterion"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write nₖ = trineDir(k) and S(t,a) = scalarB(t,a) = tI + a·σ. "
                            + "The explicit coordinates agree with the cosine and sine expressions "
                            + "at angles 2(k + 1)π/3. They give ‖nₖ‖ = 1 and ∑ₖ nₖ = 0. "
                            + "For every sign string s, the vector aₛ = ∑ₖ sgn(s(k))nₖ is zero "
                            + "when all signs agree and is either 2nⱼ or −2nⱼ otherwise. "
                            + "Consequently ‖aₛ‖ ≤ 2.")),
                    Paragraph(Text(
                        "The map (t,a) ↦ S(t,a) is injective: the real diagonal entries determine "
                            + "t and the z coordinate, while the real and imaginary parts of the "
                            + "upper-right entry determine the x and y coordinates. Also S(1,0) = I, "
                            + "and an effect has scalar coordinate (1 + sgn(x)b)/2 and vector "
                            + "coordinate (η sgn(x)/2)nₖ.")),
                    Paragraph(Text(
                        "Suppose a common parent G exists. Decompose each Hermitian matrix as "
                            + "G(s) = S(qₛ,rₛ), with qₛ = Re(trace(G(s)))/2 and rₛ equal to one half "
                            + "of its Bloch vector. The positivity criterion for S gives ‖rₛ‖ ≤ qₛ. "
                            + "Additivity of S and injectivity of its coordinates turn ∑ₛ G(s) = I "
                            + "into ∑ₛ qₛ = 1. Applying the same coordinate comparison to each marginal "
                            + "gives ∑ over s with s(k) = x of rₛ = (η sgn(x)/2)nₖ. Subtracting "
                            + "the false marginal from the true marginal yields ∑ₛ sgn(s(k))rₛ = ηnₖ.")),
                    Paragraph(Text(
                        "Interchange the finite sums and take real inner products with the unit "
                            + "vectors nₖ. The marginal identities imply ∑ₛ ⟨aₛ,rₛ⟩ = 3η. "
                            + "Cauchy–Schwarz and the bound on aₛ give "
                            + "3η ≤ ∑ₛ 2‖rₛ‖ ≤ ∑ₛ 2qₛ = 2. Together with the assumed "
                            + "|b| ≤ 1 − η, this proves η ≤ trineThreshold(b) in all three branches.")),
                    Paragraph(Text(
                        "For the converse, enumerate the eight sign strings. For each k let mₖ "
                            + "be the string with its only false entry at k, and let pₖ be its "
                            + "pointwise complement. Given real c,d,u,v,e,f, assign S(c,−unₖ) to mₖ, "
                            + "S(d,vnₖ) to pₖ, S(e,0) to the all-true string and S(f,0) to the "
                            + "all-false string. The sum of these matrices is S(3c + 3d + e + f,0). "
                            + "The true marginal at k is S(2c + d + e,(u + v)nₖ), and the false "
                            + "marginal is S(c + 2d + f,−(u + v)nₖ). These identities follow by "
                            + "expanding the eight matrices and their entries.")),
                    Paragraph(Text(
                        "The positivity criterion makes all eight matrices positive semidefinite "
                            + "whenever |u| ≤ c, |v| ≤ d, 0 ≤ e and 0 ≤ f. The equations "
                            + "2c + d + e = (1 + b)/2, c + 2d + f = (1 − b)/2 and u + v = η/2 "
                            + "then give the required marginals. Adding the first two equations "
                            + "gives 3c + 3d + e + f = 1, so their total is I. Thus these inequalities "
                            + "and equations suffice to construct a common parent.")),
                    Paragraph(Text(
                        "When −1/3 ≤ b ≤ 1/3 and 0 ≤ η ≤ 2/3, take c = (1 + 3b)/6, "
                            + "d = (1 − 3b)/6, u = c(3η/2), v = d(3η/2), e = f = 0. "
                            + "Here c,d ≥ 0 and 0 ≤ 3η/2 ≤ 1, so |u| ≤ c and |v| ≤ d; "
                            + "the three marginal equations follow by substitution.")),
                    Paragraph(Text(
                        "When b ≥ 1/3 and 0 ≤ η ≤ 1 − b, take c = (1 − b)/2, d = 0, "
                            + "u = η/2, v = 0, e = (3b − 1)/2, f = 0. When b ≤ −1/3 and "
                            + "0 ≤ η ≤ 1 + b, take c = 0, d = (1 + b)/2, u = 0, v = η/2, "
                            + "e = 0, f = (−1 − 3b)/2. Each choice satisfies the positivity "
                            + "inequalities and the three marginal equations.")),
                    Paragraph(Text(
                        "Finally, expand the definition of trineThreshold in the inequality "
                            + "η ≤ trineThreshold(b). Its first branch uses the negative-bias "
                            + "construction, its second uses the central construction, and its last "
                            + "uses the positive-bias construction. Both endpoints −1/3 and 1/3 "
                            + "belong to the central branch. This proves sufficiency and completes "
                            + "the equivalence on the full stated domain."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yadavalli-andrejic-kunjwal-2024-biased-trine-joint-measurability"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula TrineDirFormula()
    {
        Formula root = At(Qualified("Real", "sqrt"), D(3));
        Formula directions = Vector(
            Vector(Fraction(Negate(D(1)), D(2)), D(0), Fraction(root, D(2))),
            Vector(Fraction(Negate(D(1)), D(2)), D(0), Fraction(Negate(root), D(2))),
            Vector(D(1), D(0), D(0)));
        return All("i", Fin(3), Equal(Typed(LocalCall("trineDir", X("i")), Vectors()),
            At(Qualified("WithLp", "toLp"), D(2), At(directions, X("i")))));
    }

    private static Formula TrineEffectFormula() => All("b", Reals(), All("η", Reals(),
        All("k", Fin(3), All("x", Qualified("Bool"),
            Equal(Typed(LocalCall("trineEffect", X("b"), X("η"), X("k"), X("x")), Matrices()),
                Smul(Typed(Fraction(D(1), D(2)), Complexes()),
                    At(Qualified("D5", "S3", "Quantum", "Measurement", "FourQubitParentConstruction", "scalarB"),
                        Add(D(1), Multiply(Sign(X("x")), X("b"))),
                        Smul(Multiply(X("η"), Sign(X("x"))), LocalCall("trineDir", X("k"))))))))));

    private static Formula JointMeasurabilityFormula() => All("b", Reals(), All("η", Reals(),
        Equivalence(LocalCall("TriplewiseJointlyMeasurable", X("b"), X("η")),
            At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "HeisenbergChannelCompressionEquivalence",
                "FamilyJointlyMeasurable"), LocalCall("trineEffect", X("b"), X("η"))))));

    private static Formula ThresholdFormula() => All("b", Reals(),
        Equal(Typed(LocalCall("trineThreshold", X("b")), Reals()),
            At(Qualified("ite"), LT(X("b"), Fraction(Negate(D(1)), D(3))), Add(D(1), X("b")),
                At(Qualified("ite"), LE(X("b"), Fraction(D(1), D(3))), Fraction(D(2), D(3)),
                    Subtract(D(1), X("b"))))));

    private static Formula ResultFormula() => All("b", Reals(), All("η", Reals(),
        Arrow(LE(Negate(D(1)), X("b")), Arrow(LE(X("b"), D(1)),
        Arrow(LE(D(0), X("η")), Arrow(LE(X("η"), D(1)),
        Arrow(LE(new Formula.Absolute(X("b")), Subtract(D(1), X("η"))),
            Equivalence(LocalCall("TriplewiseJointlyMeasurable", X("b"), X("η")),
                LE(X("η"), LocalCall("trineThreshold", X("b")))))))))));

    private static Formula LocalCall(string name, params Formula[] args) =>
        At(Qualified("D5", "S3", "Quantum", "Measurement", "BiasedTrineJointMeasurabilityThreshold", name), args);
    private static Formula Sign(Formula x) =>
        At(Qualified("D5", "S3", "Combinatorics", "IsingUniquenessSets", "sgn"), x);
    private static Formula X(string name) => name == "η"
        ? new Formula.Symbol(FormulaIdentifier.Create("eta")) : F.Id(name);
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte n) => At(Qualified("Fin"), D(n));
    private static Formula Vectors() => At(Qualified("EuclideanSpace"), Reals(), Fin(3));
    private static Formula Matrices() => At(Qualified("Matrix"), Fin(2), Fin(2), Complexes());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Vector(Formula a, Formula b, Formula c) =>
        Seq(Bang, OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket);
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negate(Formula value) => new Formula.Negate(value);
    private static Formula LT(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Equivalence(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
