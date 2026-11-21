using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class ReflectionInvariantBornFormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/ReflectionInvariantBornForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized quadratic reading invariant under one reflection is the Born weight.",
        H("The Born form from one reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflection-invariant-born-form"),
                DeclarationHandle.Create(Module + "eq_norm_inner_sq_of_reflection_invariant"),
                H("A reflection-invariant normalized reading is the Born weight"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a complex inner product space, φ a vector of E and g a real "
                        + "function on E. Assume five conditions on g: g(cψ) = |c|² g(ψ) for every "
                        + "complex scalar c and every ψ; the parallelogram law "
                        + "g(zφ + w) + g(zφ − w) = 2 g(zφ) + 2 g(w) for every complex z and every w "
                        + "orthogonal to φ; g is unchanged by the map ψ ↦ 2⟨φ, ψ⟩φ − ψ at every unit "
                        + "vector ψ; g(φ) = 1; and g vanishes at every unit vector orthogonal to φ. "
                        + "Then g(ψ) = |⟨φ, ψ⟩|² for every ψ in E. The statement concerns one vector "
                        + "φ; applied to each φ in turn, it gives the same conclusion for a reading "
                        + "f(ψ, φ) under the five conditions at every φ. Neither finite dimension "
                        + "nor completeness is assumed.")),
                    Paragraph(Text(
                        "Proof: the conditions force ‖φ‖ = 1. Homogeneity at c = 0 gives g(0) = 0, "
                        + "so φ ≠ 0; with r = ‖φ‖, the map sends the unit vector φ/r to "
                        + "(2r − 1/r)φ, and homogeneity with g(φ) = 1 turns invariance into "
                        + "(2r − 1/r)² = 1/r², that is (2r² − 1)² = 1, whose only positive "
                        + "solution is r = 1. The map is then the reflection that fixes φ and "
                        + "reverses its orthogonal complement. Homogeneity extends the invariance "
                        + "from unit vectors to all vectors, since the reflection commutes with "
                        + "complex scalars. Write ψ = zφ + w with z = ⟨φ, ψ⟩ and w orthogonal to φ. "
                        + "Rescaling w to a unit vector and using homogeneity gives g(w) = 0, and "
                        + "g(zφ) = |z|² g(φ) = |z|². The reflection sends zφ + w to zφ − w, so "
                        + "invariance makes the two terms on the left of the parallelogram law for "
                        + "zφ and w equal; the law then gives 2 g(ψ) = 2|z|² + 0.")),
                    Paragraph(Text(
                        "A Hermitian quadratic form ψ ↦ Re⟨ψ, Tψ⟩ with T complex linear satisfies "
                        + "homogeneity and the parallelogram law for all pairs, so the theorem "
                        + "applies to such readings; any unitary covariance that includes the "
                        + "reflection fixing φ supplies the invariance condition.")),
                    Paragraph(Text(
                        "Each of the five conditions is needed. In each example below φ is a unit "
                        + "vector, χ is a unit vector orthogonal to φ, and the function satisfies "
                        + "the four other conditions. Without g(φ) = 1: g = 0 differs from "
                        + "|⟨φ, ψ⟩|² at ψ = φ. Without vanishing on the orthogonal complement: "
                        + "g(ψ) = ‖ψ‖² equals 1 at χ, where |⟨φ, χ⟩|² = 0. Without invariance "
                        + "under the reflection: g(ψ) = |⟨φ, ψ⟩|² + Re(conj⟨φ, ψ⟩ ⟨χ, ψ⟩) equals "
                        + "2 at φ + χ, where |⟨φ, φ + χ⟩|² = 1. Without the parallelogram law: "
                        + "g(ψ) = |⟨φ, ψ⟩|⁴ / ‖ψ‖² for ψ ≠ 0, with g(0) = 0, equals 1/2 at φ + χ, "
                        + "where |⟨φ, φ + χ⟩|² = 1, and the law fails for the pair (φ, χ). With "
                        + "homogeneity required only for real scalars: g(ψ) = (Re⟨φ, ψ⟩)² "
                        + "satisfies it and the four other conditions, yet vanishes at ψ = iφ, "
                        + "where |⟨φ, ψ⟩|² = 1.")),
                    Paragraph(Text(
                        "The result is an elementary argument; no published source stating it in "
                        + "this form is known, and nothing is claimed as new."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle, Underscore, Grp(Complex));

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
        Formula z = V("z"), w = V("w");
        Formula Read(Formula x) => Call("g", x);
        Formula zphi = Call("smul", z, phi);

        Formula hsmul = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("c"), Complex,
            All(e, Equal(Read(Call("smul", c, psi)), Mul(Sq(NormOf(c)), Read(psi))), "psi"));
        Formula hpar = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("z"), Complex,
            All(e, Implies(Equal(Inner(phi, w), D(0)),
                    Equal(Add(Read(Add(zphi, w)), Read(Sub(zphi, w))),
                        Add(Mul(D(2), Read(zphi)), Mul(D(2), Read(w))))),
                "w"));
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

        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("E"),
            F.Id("Type"),
            Seq(OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
                OpenBracket, Call("InnerProductSpace", Complex, e), CloseBracket, Sp, body)));
    }
}
