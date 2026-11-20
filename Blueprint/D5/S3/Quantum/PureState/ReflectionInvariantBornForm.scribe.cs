using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class ReflectionInvariantBornFormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/ReflectionInvariantBornForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized quadratic reading invariant under one reflection fixing the reference vector is the Born weight.",
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
                        "Let E be a complex inner product space and f(ψ, φ) a real number for each "
                        + "pair of vectors. For every unit vector φ assume five conditions on the map "
                        + "ψ ↦ f(ψ, φ): it scales by |c|² when ψ is multiplied by a complex scalar c; "
                        + "it satisfies the parallelogram law f(ψ + χ, φ) + f(ψ − χ, φ) = "
                        + "2 f(ψ, φ) + 2 f(χ, φ); it is unchanged by the reflection "
                        + "ψ ↦ 2⟨φ, ψ⟩φ − ψ, which fixes φ and reverses its orthogonal complement; it "
                        + "equals 1 at ψ = φ; and it vanishes at every unit vector ψ orthogonal to φ. "
                        + "Then f(ψ, φ) = |⟨φ, ψ⟩|² for every vector ψ and every unit vector φ. No "
                        + "condition relates the readings for different φ, and neither finite "
                        + "dimension nor completeness is assumed.")),
                    Paragraph(Text(
                        "Proof: write ψ = zφ + w with z = ⟨φ, ψ⟩ and w orthogonal to φ. Rescaling w "
                        + "to a unit vector and using the scaling condition gives f(w, φ) = 0, and "
                        + "f(zφ, φ) = |z|² f(φ, φ) = |z|². The reflection sends zφ + w to zφ − w, so "
                        + "invariance makes the two terms on the left of the parallelogram law for "
                        + "zφ and w equal; the law then gives 2 f(ψ, φ) = 2|z|² + 0.")),
                    Paragraph(Text(
                        "A Hermitian quadratic form ψ ↦ Re⟨ψ, Tψ⟩ with T complex linear satisfies "
                        + "the scaling condition and the parallelogram law, so the theorem applies to "
                        + "such readings; any unitary covariance that includes the reflection fixing "
                        + "φ supplies the invariance condition. The parallelogram law cannot be "
                        + "dropped: f(ψ, φ) = |⟨φ, ψ⟩|⁴ / ‖ψ‖² for ψ ≠ 0, with f(0, φ) = 0, "
                        + "scales by |c|², is invariant under "
                        + "the reflection, equals 1 at φ and vanishes on orthogonal unit vectors, "
                        + "yet at ψ = (φ + χ)/√2 with χ a unit vector orthogonal to φ it equals 1/4 "
                        + "while |⟨φ, ψ⟩|² = 1/2. Homogeneity under complex scalars cannot be "
                        + "weakened to real scalars: f(ψ, φ) = (Re⟨φ, ψ⟩)² satisfies all other "
                        + "conditions and the scaling condition for real c, yet vanishes at ψ = iφ, "
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

    private static Formula Read(Formula psi, Formula phi) => Call("f", psi, phi);

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
        Formula phi = V("phi"), psi = V("psi"), chi = V("chi"), c = V("c");

        Formula hsmul = All(e, Implies(Unit(phi), new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("c"), Complex,
                All(e, Equal(Read(Call("smul", c, psi), phi), Mul(Sq(NormOf(c)), Read(psi, phi))),
                    "psi"))),
            "phi");
        Formula hpar = All(e, Implies(Unit(phi), All(e,
                Equal(Add(Read(Add(psi, chi), phi), Read(Sub(psi, chi), phi)),
                    Add(Mul(D(2), Read(psi, phi)), Mul(D(2), Read(chi, phi)))),
                "psi", "chi")),
            "phi");
        Formula hrefl = All(e, Implies(Unit(phi),
                Equal(Read(Sub(Call("smul", Mul(D(2), Inner(phi, psi)), phi), psi), phi),
                    Read(psi, phi))),
            "phi", "psi");
        Formula hone = All(e, Implies(Unit(phi), Equal(Read(phi, phi), D(1))), "phi");
        Formula hzero = All(e, Implies(Unit(phi), Implies(Unit(psi),
                Implies(Equal(Inner(phi, psi), D(0)), Equal(Read(psi, phi), D(0))))),
            "phi", "psi");
        Formula conclusion = All(e,
            Implies(Unit(phi), Equal(Read(psi, phi), Sq(NormOf(Inner(phi, psi))))),
            "phi", "psi");

        Formula body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("f"),
            new Formula.TypeArrow(e, new Formula.TypeArrow(e, Reals)),
            Implies(hsmul, Implies(hpar, Implies(hrefl, Implies(hone, Implies(hzero, conclusion))))));

        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("E"),
            F.Id("Type"),
            Seq(OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
                OpenBracket, Call("InnerProductSpace", Complex, e), CloseBracket, Sp, body)));
    }
}
