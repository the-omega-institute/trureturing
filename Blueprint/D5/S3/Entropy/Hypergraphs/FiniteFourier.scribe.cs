using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Hypergraphs;

internal sealed class FiniteFourierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/Hypergraphs/FiniteFourier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fourier inversion, Gaussian point bounds and entropy estimates.",
        H("Finite uniform laws: Fourier and entropy estimates"),
        Blocks(
            Paragraph(Text("Throughout, Ω is a nonempty finite type with its uniform law. " +
                "For X on Ω, p(k)=|{ω∈Ω:X(ω)=k}|/|Ω|. For integer-valued X, " +
                "φ_X(t)=|Ω|⁻¹ Σω exp(X(ω) i t), with real t and complex exponential. " +
                "For natural-valued X bounded by n, H(X)=Σ_{k=0}^n -p(k) log₂ p(k), " +
                "with the summand zero at p(k)=0. The circular-orientation proof applies the point-mass " +
                "bound to the number of vertices of a prescribed indegree.")),
            Node("finite_uniform_mass_bound", "A point-mass bound from characteristic-function decay",
                All("X", Arrow(Id("Omega"), Integers()), All("k", Integers(), All("A", Reals(),
                    Implies(Lt(Num(0), Id("A")), Implies(
                        All("t", Reals(), Le(new Formula.Norm(Call("phi", Id("t"))),
                            Call("exp", new Formula.Negate(Multiply(Id("A"),
                                new Formula.Power(Call("sin", Frac(Id("t"), Num(2))), Num(2))))))),
                        Le(Call("p", Id("k")), Frac(Call("sqrt", Id("pi")),
                            Multiply(Num(2), Call("sqrt", Id("A")))))))))),
                "Ω is universally quantified with Fintype and Nonempty instances. X:Ω→ℤ, k:ℤ and " +
                "A:ℝ are arbitrary. The characteristic-function bound is required for every real t. " +
                "Finite Fourier inversion on [-π,π], sin(|t|/2)≥|t|/π and the Gaussian integral " +
                "give √π/(2√A). This auxiliary does not assert that a particular orientation law " +
                "satisfies the characteristic-function hypothesis."),
            Node("finite_entropy_lower", "Entropy from a uniform upper bound on every atom",
                All("X", Arrow(Id("Omega"), Naturals()), All("n", Naturals(),
                    Implies(All("omega", Id("Omega"), Le(Call("X", Id("omega")), Id("n"))),
                        All("C", Reals(), Implies(Lt(Num(0), Id("C")),
                            Implies(All("k", Naturals(), Le(Call("p", Id("k")), Id("C"))),
                                Le(new Formula.Negate(Call("logb", Num(2), Id("C"))),
                                    Call("H", Id("X"))))))))),
                "Ω is again any nonempty finite type. The support bound X(ω)≤n holds for every ω, " +
                "and p(k)≤C is assumed for every natural k, not just a designated atom. " +
                "The displayed finite entropy includes every index in Finset.range(n+1). " +
                "The proof uses normalization and monotonicity of the base-two logarithm on positive masses."),
            Node("finite_mass_le_one", "Every atom has probability at most one",
                All("X", Arrow(Id("Omega"), Naturals()), All("k", Naturals(),
                    Le(Call("p", Id("k")), Num(1)))),
                "For any nonempty finite Ω, any X:Ω→ℕ and any k:ℕ, the fibre cardinality is at most " +
                "the total cardinality. This bound is also consumed in the small-n entropy branch."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("circular-finite-fourier-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula Integers() => F.Seq(F.Mathbb, F.Grp(Id("Z")));
    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
}
