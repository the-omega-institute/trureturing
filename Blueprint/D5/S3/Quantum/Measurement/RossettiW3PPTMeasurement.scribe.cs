using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class RossettiW3PPTMeasurementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/rossetti2025observational");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal three-qubit W-state PPT measurement is not fully separable.",
        H("The complementary W-state effect is not fully separable"), Blocks(
            Paragraph(Text("A basis index x : Fin 3 → Fin 2 lists the bits of the three qubits in order. "
                + "Pi.single x 1 is the computational basis vector |x⟩. "
                + "Matrix.vecMulVec u (star u) is the rank-one operator |u⟩⟨u|. "
                + "Complex.ofReal is the coercion from real to complex numbers. "
                + "The identity in the formulas is the identity matrix on this eight-dimensional space.")),
            Node("W3", "The three-qubit W state", Equal(Typed(Named("W3"), Vectors()), WBody(false)),
                "Section X.0.4, printed page 22, uses |W₃⟩ = √(1/3)(|100⟩ + |010⟩ + |001⟩). "
                + "The square root is real and is then embedded in the complex scalars.", AssessedProvenance.FromLiterature(Source)),
            Node("W3bar", "The anti-W state", Equal(Typed(Named("W3bar"), Vectors()), WBody(true)),
                "Section X.0.4, printed page 22, defines |W̄₃⟩ = √(1/3)(|011⟩ + |101⟩ + |110⟩). "
                + "The three terms have Hamming weight two.", AssessedProvenance.FromLiterature(Source)),
            Node("P1", "The weight-one projector", Equal(Typed(Named("P1"), Matrices()), WeightProjector(false)),
                ProjectorQuote() + "On printed page 22, P₁ is the sum of the three computational-basis projectors of weight one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("P2", "The weight-two projector", Equal(Typed(Named("P2"), Matrices()), WeightProjector(true)),
                ProjectorQuote() + "On printed page 22, P₂ is the sum of the three computational-basis projectors of weight two.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Q1", "The W-state projector", Equal(Typed(Named("Q1"), Matrices()), RankOne(Named("W3"))),
                ProjectorQuote() + "The first of the six invariant projectors on printed page 22 is Q₁ = |W₃⟩⟨W₃|.", AssessedProvenance.FromLiterature(Source)),
            Node("Q2", "The anti-W projector", Equal(Typed(Named("Q2"), Matrices()), RankOne(Named("W3bar"))),
                ProjectorQuote() + "The second invariant projector is Q₂ = |W̄₃⟩⟨W̄₃|.", AssessedProvenance.FromLiterature(Source)),
            Node("Q3", "The remaining weight-one subspace", Equal(Typed(Named("Q3"), Matrices()),
                    Subtract(Named("P1"), RankOne(Named("W3")))),
                ProjectorQuote() + "Q₃ subtracts the W-state projector from P₁. The source uses W₃ for the projector in this subtraction.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Q4", "The remaining weight-two subspace", Equal(Typed(Named("Q4"), Matrices()),
                    Subtract(Named("P2"), RankOne(Named("W3bar")))),
                ProjectorQuote() + "Q₄ subtracts the anti-W projector from P₂. The source uses W̄₃ for the projector in this subtraction.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Q5", "The zero-weight projector", Equal(Typed(Named("Q5"), Matrices()), RankOne(Basis(0, 0, 0))),
                ProjectorQuote() + "The fifth invariant projector is Q₅ = |000⟩⟨000|.", AssessedProvenance.FromLiterature(Source)),
            Node("Q6", "The weight-three projector", Equal(Typed(Named("Q6"), Matrices()), RankOne(Basis(1, 1, 1))),
                ProjectorQuote() + "The sixth invariant projector is Q₆ = |111⟩⟨111|.", AssessedProvenance.FromLiterature(Source)),
            Node("Mprime", "The optimal PPT effect from equation (83)", Equal(Typed(Named("Mprime"), Matrices()), MBody()),
                "Equation (83), printed page 23: “t₂ = 1/2, t₃ = t₄ = 0, t₅ = 2/3, t₆ = 1/12”. "
                + "All six terms are displayed, including the zero coefficients of Q₃ and Q₄.", AssessedProvenance.FromLiterature(Source)),
            Node("IsSEPEffect", "Effects proportional to fully separable states", SepFormula(),
                "After equation (62), printed page 17: “In other words, the POVM elements are proportional to separable states.” "
                + "The real proportionality constant is nonnegative. IsFullySeparableLocal is the finite convex-mixture "
                + "definition from FullySeparableExchangeObstruction, with three sites and two local basis states.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "SEP membership of the specified two-outcome measurement",
                IffTo(Named("claim"), ClaimBody()),
                "Printed page 23: “Nevertheless, none of the tests conducted so far have succeeded in detecting entanglement, "
                + "leaving open the question of whether (M′, 𝟙 − M′) belongs to the SEP class.” "
                + "The proposition says that each of the two displayed effects is proportional to a fully separable state.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("rossetti-w3-ppt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("This two-outcome measurement is outside SEP"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Put R = 𝟙 − M′. The quadratic form of R vanishes at |100⟩ + |010⟩ + |001⟩. "
                    + "The partial-transpose quadratic forms vanish at 2|000⟩ + |110⟩ + |101⟩, "
                    + "2|000⟩ + |110⟩ + |011⟩, and 2|000⟩ + |101⟩ + |011⟩ for the respective sites. "
                    + "In a sum of positive product operators these zeros force every summand to have "
                    + "weight-two diagonal mass twice its weight-one mass, including when a local diagonal vanishes. "
                    + "The same relation holds for their sum. For R the masses are 5/2 and 2, so the relation fails. "
                    + "Thus the complementary effect is not fully separable. This conclusion concerns the specified "
                    + "measurement; the optimal SEP entropy and the possible attainment of trace 9/4 by another "
                    + "SEP measurement remain separate questions."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("rossetti-w3-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static string ProjectorQuote() => "The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. ";
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Qualified(string owner, string name, params Formula[] arguments) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Bits() => new Formula.TypeArrow(Call("Fin", D(3)), Call("Fin", D(2)));
    private static Formula Vectors() => new Formula.TypeArrow(Parenthesized(Bits()), Complex());
    private static Formula Matrices() => Call("Matrix", Parenthesized(Bits()), Parenthesized(Bits()), Complex());
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Scale(Formula scalar, Formula vector) => Qualified("HSMul", "hSMul", scalar, vector);
    private static Formula Rational(byte numerator, byte denominator) => new Formula.Fraction(new Formula.Number(numerator), new Formula.Number(denominator));
    private static Formula Basis(byte a, byte b, byte c) => Qualified("Pi", "single",
        Seq(Bang, OpenBracket, D(a), Comma, Sp, D(b), Comma, Sp, D(c), CloseBracket), Typed(D(1), Complex()));
    private static Formula RankOne(Formula vector) => Qualified("Matrix", "vecMulVec", vector, Call("star", vector));
    private static Formula WeightVector(bool two) => two
        ? Add(Add(Basis(0, 1, 1), Basis(1, 0, 1)), Basis(1, 1, 0))
        : Add(Add(Basis(1, 0, 0), Basis(0, 1, 0)), Basis(0, 0, 1));
    private static Formula WBody(bool two) => Scale(
        Qualified("Complex", "ofReal", Qualified("Real", "sqrt", Rational(1, 3))), Parenthesized(WeightVector(two)));
    private static Formula WeightProjector(bool two) => two
        ? Add(Add(RankOne(Basis(0, 1, 1)), RankOne(Basis(1, 0, 1))), RankOne(Basis(1, 1, 0)))
        : Add(Add(RankOne(Basis(1, 0, 0)), RankOne(Basis(0, 1, 0))), RankOne(Basis(0, 0, 1)));
    private static Formula MBody() => Add(Add(Add(Add(Add(Named("Q1"),
        Scale(Typed(Rational(1, 2), Complex()), Named("Q2"))), Scale(Typed(D(0), Complex()), Named("Q3"))),
        Scale(Typed(D(0), Complex()), Named("Q4"))), Scale(Typed(Rational(2, 3), Complex()), Named("Q5"))),
        Scale(Typed(Rational(1, 12), Complex()), Named("Q6")));
    private static Formula SepFormula() => All("E", Matrices(), IffTo(Call("IsSEPEffect", F.Id("E")),
        Some("c", Real(), Some("rho", Matrices(), And(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, F.Id("c")),
            And(Qualified("FullySeparableExchangeObstruction", "IsFullySeparableLocal", F.Id("rho")),
                Equal(F.Id("E"), Scale(Qualified("Complex", "ofReal", F.Id("c")), F.Id("rho")))))))));
    private static Formula ClaimBody() => And(Call("IsSEPEffect", Named("Mprime")),
        Call("IsSEPEffect", Parenthesized(Subtract(Typed(D(1), Matrices()), Named("Mprime")))));
}
