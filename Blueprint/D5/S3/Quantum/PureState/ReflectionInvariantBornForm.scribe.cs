using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class ReflectionInvariantBornFormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/ReflectionInvariantBornForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real reading on an inner product space over the real or complex numbers that is quadratic, equal to one at a vector φ, zero on the orthogonal complement of φ and invariant under the reflection fixing φ is the Born weight |⟨φ, ψ⟩|².",
        H("The Born form from one reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflection-invariant-born-form"),
                DeclarationHandle.Create(Module + "eq_norm_inner_sq_of_reflection_invariant"),
                H("A quadratic reading fixed by one reflection is the Born weight"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be the real or the complex numbers (an RCLike field), E an inner "
                        + "product space over k, φ a vector of E and g a real function on E. Assume "
                        + "five conditions on g: g(cψ) = |c|² g(ψ) for every scalar c in k and every "
                        + "ψ; the parallelogram law g(φ + w) + g(φ − w) = 2 g(φ) + 2 g(w) for every w "
                        + "orthogonal to φ; g is unchanged by the map ψ ↦ 2⟨φ, ψ⟩φ − ψ at every unit "
                        + "vector ψ; g(φ) = 1; and g vanishes at every unit vector orthogonal to φ. "
                        + "Then g(ψ) = |⟨φ, ψ⟩|² for every ψ in E. The parallelogram law for the "
                        + "pairs (zφ, w) with z in k and w orthogonal to φ follows from the law for "
                        + "the pairs (φ, w) by homogeneity, since zφ ± w = z(φ ± z⁻¹w) for z ≠ 0. "
                        + "For k the real numbers the conclusion reads g(ψ) = ⟨φ, ψ⟩², and "
                        + "homogeneity is required only for real scalars. The statement concerns one "
                        + "vector φ; applied to each φ in turn, it gives the same conclusion for a "
                        + "reading f(ψ, φ) under the five conditions at every φ. Neither finite "
                        + "dimension nor completeness is assumed.")),
                    Paragraph(Text(
                        "Proof: the conditions force ‖φ‖ = 1. Homogeneity at c = 0 gives g(0) = 0, "
                        + "so φ ≠ 0; with r = ‖φ‖, the map sends the unit vector φ/r to "
                        + "(2r − 1/r)φ, and homogeneity with g(φ) = 1 turns invariance into "
                        + "(2r − 1/r)² = 1/r², that is (2r² − 1)² = 1, whose only positive "
                        + "solution is r = 1. The map is then the reflection that fixes φ and "
                        + "reverses its orthogonal complement. Homogeneity extends the invariance "
                        + "from unit vectors to all vectors, since the reflection commutes with "
                        + "scalars. Write ψ = zφ + w with z = ⟨φ, ψ⟩ and w orthogonal to φ. "
                        + "Rescaling w to a unit vector and using homogeneity gives g(w) = 0, and "
                        + "g(zφ) = |z|² g(φ) = |z|². The reflection sends zφ + w to zφ − w, so "
                        + "invariance makes the two terms on the left of the parallelogram law for "
                        + "zφ and w equal; the law then gives 2 g(ψ) = 2|z|² + 0.")),
                    Paragraph(Text(
                        "A Hermitian quadratic form ψ ↦ Re⟨ψ, Tψ⟩ with T linear over k satisfies "
                        + "homogeneity and the parallelogram law for all pairs, so the theorem "
                        + "applies to such readings. For a unit vector φ the map ψ ↦ 2⟨φ, ψ⟩φ − ψ "
                        + "is the unitary reflection fixing φ, so any unitary covariance that "
                        + "includes it supplies the invariance condition. The quadratic-like "
                        + "readings IsQuadraticLike of the module GleasonComplexRepresentation are "
                        + "required to be homogeneous, to satisfy the parallelogram law for all "
                        + "pairs, to be nonnegative and to be bounded by the squared norm, on the "
                        + "finite-dimensional space ℂ^N; the present theorem assumes neither finite "
                        + "dimension, nor positivity, nor the parallelogram law beyond the pairs "
                        + "(φ, w) with w orthogonal to φ.")),
                    Paragraph(Text(
                        "The following written argument, which is not stated as a theorem here, "
                        + "shows that each of the five conditions is needed. In each example below "
                        + "φ is a unit vector, χ is a unit vector orthogonal to φ, and the function "
                        + "satisfies the four other conditions. Without g(φ) = 1: g = 0 differs from "
                        + "|⟨φ, ψ⟩|² at ψ = φ. Without vanishing on the orthogonal complement: "
                        + "g(ψ) = ‖ψ‖² equals 1 at χ, where |⟨φ, χ⟩|² = 0. Without invariance "
                        + "under the reflection: g(ψ) = |⟨φ, ψ⟩|² + Re(conj⟨φ, ψ⟩ ⟨χ, ψ⟩) equals "
                        + "2 at φ + χ, where |⟨φ, φ + χ⟩|² = 1. Without the parallelogram law: "
                        + "g(ψ) = |⟨φ, ψ⟩|⁴ / ‖ψ‖² for ψ ≠ 0, with g(0) = 0, equals 1/2 at φ + χ, "
                        + "where |⟨φ, φ + χ⟩|² = 1, and the law fails for the pair (φ, χ). For a "
                        + "complex space with homogeneity required only for real scalars: "
                        + "g(ψ) = (Re⟨φ, ψ⟩)² satisfies it and the four other conditions, yet "
                        + "vanishes at ψ = iφ, where |⟨φ, ψ⟩|² = 1.")),
                    Paragraph(Text(
                        "The result is an elementary argument; no published source stating it in "
                        + "this form is known, and nothing is claimed as new."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Field => F.Id("k");

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle, Underscore, Grp(Field));

    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));

    private static Formula NormOf(Formula x) => new Formula.Norm(x);

    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);

    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);

    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);

    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);

    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);

    private static Formula Unit(Formula x) => Equal(NormOf(x), D(1));

    private static Formula All(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), domain))],
            body);

    private static Formula TheoremFormula()
    {
        Formula e = V("E");
        Formula phi = V("phi"), psi = V("psi"), c = V("c");
        Formula w = V("w");
        Formula Read(Formula x) => Call("g", x);

        Formula hsmul = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("c"), Field,
            All(e, Equal(Read(Call("smul", c, psi)), Mul(Sq(NormOf(c)), Read(psi))), "psi"));
        Formula hpar = All(e, Implies(Equal(Inner(phi, w), D(0)),
                Equal(Add(Read(Add(phi, w)), Read(Sub(phi, w))),
                    Add(Mul(D(2), Read(phi)), Mul(D(2), Read(w))))),
            "w");
        Formula hrefl = All(e, Implies(Unit(psi),
                Equal(Read(Sub(Call("smul", Mul(D(2), Inner(phi, psi)), phi), psi)), Read(psi))),
            "psi");
        Formula hone = Equal(Read(phi), D(1));
        Formula hzero = All(e, Implies(Unit(psi),
                Implies(Equal(Inner(phi, psi), D(0)), Equal(Read(psi), D(0)))),
            "psi");
        Formula conclusion = All(e, Equal(Read(psi), Sq(NormOf(Inner(phi, psi)))), "psi");

        Formula readings = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("g"),
            new Formula.TypeArrow(e, Reals),
            Implies(hsmul, Implies(hpar, Implies(hrefl, Implies(hone, Implies(hzero, conclusion))))));
        Formula body = All(e, readings, "phi");

        Formula space = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("E"),
            F.Id("Type"),
            Seq(OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
                OpenBracket, Call("InnerProductSpace", Field, e), CloseBracket, Sp, body));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            F.Id("Type"),
            Seq(OpenBracket, Call("RCLike", Field), CloseBracket, Sp, space)));
    }
}
