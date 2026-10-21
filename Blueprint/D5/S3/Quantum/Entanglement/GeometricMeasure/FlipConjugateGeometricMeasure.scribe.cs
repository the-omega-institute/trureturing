using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GeometricMeasure;

internal sealed class FlipConjugateGeometricMeasureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/denkerimaiguhne2025chiral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The geometric measure is constant on each flip-conjugate symmetric subspace in every local dimension at least two.",
        H("The geometric measure of the flip-conjugate symmetric subspaces"),
        Blocks(
            Paragraph(Text(
                "Use the computational basis of three copies of ℂᵈ. Coordinates are indexed by "
                    + "Fin d, with the threefold index associated as Fin d × (Fin d × Fin d). "
                    + "A typed expression (d : ℝ) denotes the natural-to-real cast, and "
                    + "(r : ℂ), for real r, denotes the real-to-complex cast. Complex conjugation "
                    + "is written with an overline. All norms of coordinate vectors are Euclidean.")),
            Node("state", "Three-qudit coordinate vectors", "State", StateFormula(),
                "State d is the complex vector space of functions on the threefold computational basis. "
                    + "This coordinate description is defined for every natural dimension d.",
                AssessedProvenance.FromRepo()),
            Node("unit-vector", "Euclidean normalization", "UnitVector", UnitVectorFormula(),
                "For any finite index type and any complex coordinate vector, UnitVector means "
                    + "Euclidean norm one. The map WithLp.toLp with exponent two equips the "
                    + "same coordinates with their Euclidean norm.",
                AssessedProvenance.FromRepo()),
            Node("z", "The dimension-dependent complex coefficient", "z", ZFormula(),
                "The coefficient z_d is the one used by Denker, Imai and Gühne in the "
                    + "flip-conjugate basis. The square root and the quotient inside it are real; "
                    + "only their square root is then included into ℂ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("phi", "The flip-conjugate basis vectors", "φ", BasisFormula(false),
                "The coordinate formula is the computational-basis expansion of "
                    + "φ_n = (conj(z_d) ∑ᵢ |i n i⟩ + z_d ∑ᵢ |i i n⟩)/√(d+1). "
                    + "For d at least two these vectors form an orthonormal family.",
                AssessedProvenance.FromLiterature(Source)),
            Node("phi-bar", "The conjugate basis vectors", "φbar", BasisFormula(true),
                "Interchanging z_d and its conjugate gives the coordinatewise conjugate "
                    + "of φ_n, with the same real normalization factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("subspace", "The flip-conjugate symmetric subspace", "H_I", SubspaceFormula(false),
                "The complex span of the vectors φ_n is the flip-conjugate symmetric "
                    + "subspace H_I of the source. For d at least two it has dimension d.",
                AssessedProvenance.FromLiterature(Source)),
            Node("conjugate-subspace", "The conjugate symmetric subspace", "H_Ibar", SubspaceFormula(true),
                "The complex span of the vectors φbar_n is the conjugate subspace H_Ibar "
                    + "of the source. Coordinatewise complex conjugation interchanges the two subspaces.",
                AssessedProvenance.FromLiterature(Source)),
            Node("overlap", "The amplitude against a product vector", "overlap", OverlapFormula(),
                "For arbitrary local coordinate vectors a, b and c, the overlap is "
                    + "⟨a ⊗ b ⊗ c, ψ⟩. Each local coordinate in the first argument is conjugated; "
                    + "normalization is imposed separately when optimizing this amplitude.",
                AssessedProvenance.FromLiterature(Source)),
            Node("overlap-set", "Squared overlaps with unit product vectors", "overlapSet", OverlapSetFormula(),
                "The set contains precisely the squared absolute overlaps with three normalized "
                    + "local vectors. The definition allows arbitrary ψ, including vectors outside "
                    + "the two symmetric subspaces.",
                AssessedProvenance.FromRepo(Source)),
            Node("geometric-measure", "The geometric measure of entanglement", "G", MeasureFormula(),
                "The geometric measure is one minus the supremum of the squared product overlaps. "
                    + "For a unit vector in a positive finite dimension this supremum is a maximum, "
                    + "so this is the geometric measure defined in the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sharp-value", "The proposed maximal squared product overlap", "sharpValue", SharpValueFormula(),
                "The dimension-dependent scalar is the squared product overlap proposed in the "
                    + "source's conjecture. Its denominator is positive whenever d is at least two.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The constant geometric measure in both subspaces", "claim", ClaimFormula(),
                "For every natural d at least two and every normalized state in either H_I or "
                    + "H_Ibar, the geometric measure equals 1 − d²/((d²−1)(d+1)). "
                    + "This is the conjecture in the source's appendix on the flip-conjugate "
                    + "symmetric subspace, with both conjugate subspaces included.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("flip-conjugate-geometric-measure-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp bound and its attaining product vector"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix d ≥ 2. The vectors φ_n are orthonormal. If ψ = ∑ₙ α_n φ_n is unit, "
                            + "then α is unit and extends to the first column of a unitary U. "
                            + "The local unitary conj(U) ⊗ U ⊗ U sends φ_0 to ψ, as in the "
                            + "source's local-unitary proposition. Local unitaries permute unit "
                            + "product vectors and preserve overlaps, so it suffices to compute the "
                            + "maximum for φ_0. Complex conjugation gives the same maximum for H_Ibar.")),
                    Paragraph(Text(
                        "Write z = z_d and, for unit b and c, set "
                            + "χ_i = conj(z) conj(b_0) conj(c_i) + z conj(c_0) conj(b_i). "
                            + "Then √(d+1) ⟨a ⊗ b ⊗ c, φ_0⟩ = ⟨a, χ⟩. "
                            + "The maximum of |⟨a, χ⟩|² over unit a equals ‖χ‖², "
                            + "attained by a = χ/‖χ‖ when χ is nonzero; for χ = 0 every unit a attains it. "
                            + "Thus the maximal squared product overlap is the maximum of ‖χ‖²/(d+1).")),
                    Paragraph(Text(
                        "Put x = |b_0|² and y = |c_0|², so x,y ∈ [0,1]. "
                            + "The coefficient identities are |z|² = d/(2(d−1)) and Re(z²) = −1/(2(d−1)). "
                            + "Cauchy–Schwarz on the remaining coordinates, followed by "
                            + "2√(x(1−x)y(1−y)) ≤ x(1−x) + y(1−y), gives "
                            + "‖χ‖² ≤ F(x,y)/(d−1), where "
                            + "F(x,y) = d(x+y) − (d/2)(x²+y²) − xy. "
                            + "The identity F(x,y) = d²/(d+1) "
                            + "− (d+1)(x+y−2d/(d+1))²/4 − (d−1)(x−y)²/4 "
                            + "shows that its maximum on the unit square is d²/(d+1), "
                            + "at x = y = d/(d+1). Dividing by (d−1)(d+1) gives "
                            + "the upper bound d²/((d²−1)(d+1)) for the squared product overlap.")),
                    Paragraph(Text(
                        "For attainment, take r = √(d/(d+1)), t = √(1/(d+1)), "
                            + "ρ = conj(z)/z, b = r e_0 + t e_1 and c = r e_0 + ρ t e_1. "
                            + "These are unit vectors since |ρ| = 1. They have x = y = d/(d+1) "
                            + "and χ = r² e_0 + 2zrt e_1, so ‖χ‖² = d²/(d²−1). "
                            + "Choosing a = χ/‖χ‖ attains the upper bound. Transport by the local "
                            + "unitaries, and then by conjugation for H_Ibar, yields the asserted "
                            + "constant geometric measure for every unit state in either subspace."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("flip-conjugate-geometric-measure-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Qualified(string owner, string name, params Formula[] arguments)
    {
        var function = Seq(Named(owner), Dot, Named(name));
        return arguments.Length == 0 ? function : At(function, arguments);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula d) => Call("Fin", d);
    private static Formula Vectors(Formula d) => Parenthesized(new Formula.TypeArrow(FinOf(d), Complexes()));
    private static Formula StateOf(Formula d) => Call("State", d);
    private static Formula ZOf(Formula d) => Call("z", d);
    private static Formula Basis(bool conjugate, Formula d, params Formula[] arguments) =>
        At(conjugate ? Seq(Overline, Grp(Varphi)) : Varphi, [d, .. arguments]);
    private static Formula Subspace(bool conjugate, Formula d) =>
        At(new Formula.Subscript(F.Id("H"), conjugate ? Seq(Overline, Grp(F.Id("I"))) : F.Id("I")), d);
    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula Tuple(Formula i, Formula j, Formula k) =>
        Parenthesized(Seq(i, Comma, Sp, Parenthesized(Seq(j, Comma, Sp, k))));
    private static Formula Cases(Formula condition) =>
        Seq(Begin, Grp(F.Id("cases")), Typed(D(1), Complexes()), Amp, condition, RowBreak,
            Typed(D(0), Complexes()), Amp, Seq(F.Text, Grp(F.Id("otherwise"))), End, Grp(F.Id("cases")));

    private static Formula StateFormula()
    {
        var d = F.Id("d");
        var indices = Parenthesized(Seq(FinOf(d), Sp, Times, Sp,
            Parenthesized(Seq(FinOf(d), Sp, Times, Sp, FinOf(d)))));
        return All(d, Naturals(), Equal(StateOf(d),
            Parenthesized(new Formula.TypeArrow(indices, Complexes()))));
    }

    private static Formula UnitVectorFormula()
    {
        var iota = F.Id("iota"); var v = F.Id("v");
        return All(iota, Seq(F.Id("Type"), Star), Seq(
            OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
            All(v, Parenthesized(new Formula.TypeArrow(iota, Complexes())),
                Logic(Call("UnitVector", v), FormulaLogicOperator.Iff,
                    Equal(new Formula.Norm(Qualified("WithLp", "toLp", D(2), v)), D(1))))));
    }

    private static Formula ZFormula()
    {
        var d = F.Id("d"); var realD = Typed(d, Reals());
        var realRoot = Root(new Formula.Fraction(Add(realD, D(1)), Subtract(realD, D(1))));
        return All(d, Naturals(), Equal(ZOf(d), new Formula.Fraction(
            Add(Typed(D(1), Complexes()), Mul(Qualified("Complex", "I"), Typed(realRoot, Complexes()))),
            Typed(D(2), Complexes()))));
    }

    private static Formula BasisFormula(bool conjugate)
    {
        var d = F.Id("d"); var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j"); var k = F.Id("k");
        var first = Cases(Logic(Equal(j, n), FormulaLogicOperator.And, Equal(k, i)));
        var second = Cases(Logic(Equal(j, i), FormulaLogicOperator.And, Equal(k, n)));
        var z = ZOf(d);
        var numerator = Add(Mul(conjugate ? z : Conjugate(z), Parenthesized(first)),
            Mul(conjugate ? Conjugate(z) : z, Parenthesized(second)));
        var denominator = Typed(Root(Add(Typed(d, Reals()), D(1))), Complexes());
        return All(d, Naturals(), All(n, FinOf(d), All(i, FinOf(d), All(j, FinOf(d), All(k, FinOf(d),
            Equal(Basis(conjugate, d, n, Tuple(i, j, k)), new Formula.Fraction(numerator, denominator)))))));
    }

    private static Formula SubspaceFormula(bool conjugate)
    {
        var d = F.Id("d");
        return All(d, Naturals(), Equal(Subspace(conjugate, d),
            Qualified("Submodule", "span", Complexes(), Qualified("Set", "range", Basis(conjugate, d)))));
    }

    private static Formula OverlapFormula()
    {
        var d = F.Id("d"); var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var i = F.Id("i"); var j = F.Id("j"); var k = F.Id("k");
        var term = Mul(Mul(Mul(Conjugate(At(a, i)), Conjugate(At(b, j))), Conjugate(At(c, k))),
            At(Psi, Tuple(i, j, k)));
        return All(d, Naturals(), All(a, Vectors(d), All(b, Vectors(d), All(c, Vectors(d),
            All(Psi, StateOf(d), Equal(Call("overlap", a, b, c, Psi),
                SumOver(i, FinOf(d), SumOver(j, FinOf(d), SumOver(k, FinOf(d), term)))))))));
    }

    private static Formula OverlapSetFormula()
    {
        var d = F.Id("d"); var t = F.Id("t"); var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var conditions = Logic(Call("UnitVector", a), FormulaLogicOperator.And,
            Logic(Call("UnitVector", b), FormulaLogicOperator.And,
                Logic(Call("UnitVector", c), FormulaLogicOperator.And,
                    Equal(t, Square(new Formula.Norm(Call("overlap", a, b, c, Psi)))))));
        var set = Seq(OpenBrace, t, Colon, Sp, Reals(), Sp, Mid, Sp,
            Ex(a, Vectors(d), Ex(b, Vectors(d), Ex(c, Vectors(d), conditions))), CloseBrace);
        return All(d, Naturals(), All(Psi, StateOf(d), Equal(Call("overlapSet", Psi), set)));
    }

    private static Formula MeasureFormula()
    {
        var d = F.Id("d");
        return All(d, Naturals(), All(Psi, StateOf(d),
            Equal(Call("G", Psi), Subtract(D(1), Call("sSup", Call("overlapSet", Psi))))));
    }

    private static Formula SharpValueFormula()
    {
        var d = F.Id("d"); var realD = Typed(d, Reals());
        return All(d, Naturals(), Equal(Call("sharpValue", d), new Formula.Fraction(Square(realD),
            Mul(Parenthesized(Subtract(Square(realD), D(1))), Parenthesized(Add(realD, D(1)))))));
    }

    private static Formula ClaimFormula()
    {
        var d = F.Id("d");
        var membership = Logic(Member(Psi, Subspace(false, d)), FormulaLogicOperator.Or,
            Member(Psi, Subspace(true, d)));
        var conclusion = Equal(Call("G", Psi), Subtract(D(1), Call("sharpValue", d)));
        return Logic(Named("claim"), FormulaLogicOperator.Iff,
            All(d, Naturals(), Logic(LE(D(2), d), FormulaLogicOperator.Implies,
                All(Psi, StateOf(d), Logic(Call("UnitVector", Psi), FormulaLogicOperator.Implies,
                    Logic(membership, FormulaLogicOperator.Implies, conclusion))))));
    }
}
