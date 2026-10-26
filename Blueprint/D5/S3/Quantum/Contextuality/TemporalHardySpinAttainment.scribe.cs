using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class TemporalHardySpinAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/choudhary2013temporalhardy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive integer n, spin-n/2 measurements attain temporal Hardy success probability one quarter.",
        H("Temporal Hardy attainment for every positive spin"), Blocks(
            Paragraph(Text(
                "Work on ℂ^(n+1) in the standard basis e_k = |n/2 − k⟩, with ℏ = 1. "
                    + "The matrices Jx(n), Jy(n) and Jz(n) are the spin-n/2 components in this basis. "
                    + "Fin(n+1) indexes the coordinates from zero through n. "
                    + "A matrix asterisk denotes the conjugate transpose, and a real scalar in "
                    + "a complex matrix or vector expression is included into ℂ.")),
            Node("spin-component", "A spin component in a real direction", "spinComponent",
                SpinComponentFormula(),
                "The spin component u·S is u₀Jx(n) + u₁Jy(n) + u₂Jz(n). "
                    + "This definition allows every real direction u; the unit-length "
                    + "conditions for the four measurement directions appear in claim."),
            Node("spectral-projector", "The projector onto an outcome eigenspace", "IsSpectralProjector",
                SpectralProjectorFormula(),
                "For complex matrices M and Π and a real outcome a, IsSpectralProjector "
                    + "requires Π to be idempotent and self-adjoint, with fixed vectors exactly "
                    + "the a-eigenvectors of M. Thus its range is the whole a-eigenspace, "
                    + "including any degeneracy, as required for a Lüders measurement in Section III."),
            Node("sequential-probability", "The sequential expectation", "seqProb",
                SequentialProbabilityFormula(),
                "The expression is defined for every complex vector ψ and every pair of "
                    + "complex matrices Π_X and Π_Y. For a unit state and orthogonal "
                    + "outcome projectors it is the sequential probability in Section III: "
                    + "first measure X and then Y. The complementary outcome uses I − Π."),
            Node("claim", "Attainability with spin measurements", "claim", ClaimFormula(),
                "For every n ≥ 1, there are four real unit directions, four real outcomes, "
                    + "their full spectral projectors, and a unit complex state ψ satisfying "
                    + "the three zero conditions and attaining success probability 1/4. "
                    + "These are the temporal Hardy conditions of Sections II and III, "
                    + "with the attainable value conjectured for every spin in the conclusion "
                    + "and Appendix B. The assertion is attainability; the dimension-independent "
                    + "upper bound is established in Section III of the source."),
            Describe.Lean(
                DescribeId.Create("temporal-hardy-spin-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A construction attaining one quarter for every positive spin"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n ≥ 1 and put r = √(2^{1/n} − 1), so r > 0 and (1 + r²)^n = 2. "
                            + "Let b_k = √C(n,k) r^k for 0 ≤ k ≤ n, where C(n,k) is the "
                            + "binomial coefficient, and set ψ = b − e₀. The binomial theorem "
                            + "gives ⟨b,b⟩ = 2, while b₀ = 1; hence ⟨ψ,ψ⟩ = 1.")),
                    Paragraph(Text(
                        "Set a = (1 − r²)/(1 + r²), c = 2r/(1 + r²), and S = a Jz(n) + c Jx(n). "
                            + "Then a² + c² = 1. The spin ladder identities give S b = (n/2)b. "
                            + "The superdiagonal entries of S are strictly positive. Its "
                            + "tridiagonal recurrence forces any eigenvector whose first "
                            + "coordinate vanishes to be zero. Consequently its n/2-eigenspace "
                            + "is exactly span{b}. The diagonal entries of Jz(n) are n/2 − k, "
                            + "so its n/2-eigenspace is exactly span{e₀}. Both eigenspaces "
                            + "are one-dimensional.")),
                    Paragraph(Text(
                        "Choose A₁ = B₂ = Jz(n), A₂ = B₁ = S, and all four outcomes n/2. "
                            + "Their spectral projectors are P = |e₀⟩⟨e₀| and Q = |b⟩⟨b|/2, "
                            + "respectively. Since Pψ = 0, Qψ = b/2, Pb = e₀ and Qe₀ = b/2, "
                            + "the probabilities ⟨ψ|PQP|ψ⟩, ⟨ψ|(I − P)P(I − P)|ψ⟩ and "
                            + "⟨ψ|Q(I − Q)Q|ψ⟩ all vanish, whereas ⟨ψ|QPQ|ψ⟩ = 1/4. "
                            + "This realizes the spin-measurement attainability conjecture "
                            + "stated in the conclusion and Appendix B."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("choudhary-goyal-konrad-ghosh-2013-temporal-hardy-spin-attainment"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("temporal-hardy-spin-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula SpinIndex(Formula n) => FinOf(Parenthesized(Add(n, D(1))));
    private static Formula Matrices(Formula n) => Call("Matrix", SpinIndex(n), SpinIndex(n), Complexes());
    private static Formula Vectors(Formula n) => Parenthesized(new Formula.TypeArrow(SpinIndex(n), Complexes()));
    private static Formula Directions() => Parenthesized(new Formula.TypeArrow(FinOf(D(3)), Reals()));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula ExMany(Formula type, Formula body, params Formula[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--) body = Ex(variables[i], type, body);
        return body;
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(params Formula[] terms)
    {
        var body = terms[^1];
        for (var i = terms.Length - 2; i >= 0; i--) body = And(terms[i], body);
        return body;
    }
    private static Formula Indexed(Formula name, string label, byte index) =>
        new Formula.Subscript(name, Seq(F.Id(label), D(index)));
    private static Formula Expectation(Formula state, Formula matrix) =>
        Seq(Langle, Sp, state, Sp, Mid, Sp, Parenthesized(matrix), Sp, Mid, Sp, state, Sp, Rangle);
    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula UnitDirection(Formula direction)
    {
        var i = F.Id("i");
        return Equal(Seq(new Formula.Subscript(Sum, Typed(i, FinOf(D(3)))), Sp,
            new Formula.Power(Parenthesized(At(direction, i)), D(2))), D(1));
    }

    private static Formula SpinComponentFormula()
    {
        var n = F.Id("n"); var u = F.Id("u");
        Formula term(byte index, string component) =>
            Mul(Call("ofReal", At(u, D(index))), Call(component, n));
        return All(n, Naturals(), All(u, Directions(), Equal(Call("spinComponent", n, u),
            Add(Add(term(0, "Jx"), term(1, "Jy")), term(2, "Jz")))));
    }

    private static Formula SpectralProjectorFormula()
    {
        var n = F.Id("n"); var m = F.Id("M"); var a = F.Id("a"); var v = F.Id("v");
        var fixedVectors = All(v, Vectors(n), IffFormula(Equal(Mul(Pi, v), v),
            Equal(Mul(m, v), Mul(Call("ofReal", a), v))));
        return All(n, Naturals(), All(m, Matrices(n), All(Pi, Matrices(n), All(a, Reals(),
            IffFormula(Call("IsSpectralProjector", m, Pi, a), Conjunction(
                Equal(new Formula.Power(Pi, D(2)), Pi),
                Equal(new Formula.Power(Pi, Star), Pi), fixedVectors))))));
    }

    private static Formula SequentialProbabilityFormula()
    {
        var n = F.Id("n");
        var px = new Formula.Subscript(Pi, F.Id("X"));
        var py = new Formula.Subscript(Pi, F.Id("Y"));
        return All(n, Naturals(), All(Psi, Vectors(n), All(px, Matrices(n), All(py, Matrices(n),
            Equal(Call("seqProb", Psi, px, py), Expectation(Psi, Mul(Mul(px, py), px)))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var ua = Indexed(F.Id("u"), "A", 1); var va = Indexed(F.Id("u"), "A", 2);
        var ub = Indexed(F.Id("u"), "B", 1); var vb = Indexed(F.Id("u"), "B", 2);
        var a = new Formula.Subscript(F.Id("a"), D(1)); var aa = new Formula.Subscript(F.Id("a"), D(2));
        var b = new Formula.Subscript(F.Id("b"), D(1)); var bb = new Formula.Subscript(F.Id("b"), D(2));
        var pa = Indexed(Pi, "A", 1); var qa = Indexed(Pi, "A", 2);
        var pb = Indexed(Pi, "B", 1); var qb = Indexed(Pi, "B", 2);
        Formula spectral(Formula direction, Formula projector, Formula outcome) =>
            Call("IsSpectralProjector", Call("spinComponent", n, direction), projector, outcome);
        Formula probability(Formula first, Formula second) => Call("seqProb", Psi, first, second);
        var conditions = Conjunction(
            UnitDirection(ua), UnitDirection(va), UnitDirection(ub), UnitDirection(vb),
            spectral(ua, pa, a), spectral(va, qa, aa), spectral(ub, pb, b), spectral(vb, qb, bb),
            Equal(Inner(Psi, Psi), D(1)),
            Equal(probability(pa, pb), D(0)),
            Equal(probability(Parenthesized(Subtract(D(1), pa)), qb), D(0)),
            Equal(probability(qa, Parenthesized(Subtract(D(1), pb))), D(0)),
            Equal(probability(qa, qb), new Formula.Fraction(D(1), D(4))));
        var witnesses = ExMany(Directions(), ExMany(Reals(), ExMany(Matrices(n),
            Ex(Psi, Vectors(n), conditions), pa, qa, pb, qb), a, aa, b, bb), ua, va, ub, vb);
        return IffFormula(Named("claim"), All(n, Naturals(), ImpliesFormula(LE(D(1), n), witnesses)));
    }
}
