using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.RotationBoxes;

internal sealed class SpinOneRotationBoxesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/Fourier/aloygalleyjonesludeschermuller2024rotationboxes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every normalized degree-two rotation family has a single quantum realization.",
        H("Spin-one rotation correlations with finitely many outcomes"),
        Blocks(
            Node("QuantumSpinOne", QuantumDefinition(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Paper),
                "Equation (4), page 7: “Note that the integers nⱼ in Eq. (4) can be arbitrary finite numbers, and so there is no a priori upper bound on the Hilbert space dimension on which the rotation box is represented.” The sigma type gives multiplicities of the three frequencies −1, 0, 1. Definition 1, page 7: “such that there exists a Hilbert space with a projective representation of SO(2) of the form (4), some quantum state (i.e. density matrix) ρ, and a POVM {Eₐ}ₐ∈𝒜 on that Hilbert space such that” P(a|θ) = Tr(UθρUθ†Eₐ). One density state and one measurement serve every real angle and every outcome. DensityState is the finite-dimensional complex density-state type; the two displayed conditions on E say that its effects are positive semidefinite and sum to the identity. The complex trace equals the real probability embedded in ℂ."),
            Node("RotationSpinOne", RotationDefinitionBody(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Paper),
                "Definition 2, page 9: “such that every one of the functions is a trigonometric polynomial of degree at most 2J in θ, and 0 ≤ P(a|θ) ≤ 1 as well as ∑ₐ∈𝒜 P(a|θ) = 1 for all θ.” The displayed expression specializes J to 1 and uses the real Fourier coefficients of Lemma 5. The five coefficient functions have the same finite outcome index A; every probability bound and the sum identity hold at every real angle."),
            Node("claim", Eqn(X("claim"), Parenthesized(ClaimBody())), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Paper),
                "Section 4.2.3, page 17: “Hence, even though the set of spin correlations ℛ₁ and 𝒬₁ agree, the corresponding GPT systems have genuinely different information-theoretic and physical behaviors. This is also the reason why we do not currently know whether 𝒬₁ᴬ = ℛ₁ᴬ for |𝒜| ≥ 3.” The proposition asserts this equality for every finite type A with at least three elements and every real probability family p. Multiplicities in the quantum realization are arbitrary finite natural numbers."),
            Node("result", ClaimBody(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Paper),
                "Every nonnegative degree-two trigonometric polynomial has a positive semidefinite three-by-three Gram representative. Averaging each representative with its reversal transpose preserves its polynomial. Probability normalization forces the sum of these averaged matrices to be diagonal with trace one. Taking inverse square roots on the nonzero diagonal support, and distributing the complementary identity equally among the outcomes, gives one complete measurement. Square roots of the diagonal entries give a pure density state, using one copy of each frequency. Conversely, the finite-multiplicity Born trace has only the five frequency differences −2, −1, 0, 1, 2. The state may depend on the family; the statement supplies no common embedding of the entire general probabilistic theory."))));

    private static DocumentBlock Node(string name, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + "." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) =>
        Seq(names.SelectMany((name, index) => index == 0
            ? new[] { Operatorname, Grp(X(name)) }
            : new[] { Dot, Operatorname, Grp(X(name)) }).ToArray());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args) =>
        Seq(new[] { function }.Concat(args.SelectMany(arg =>
            new[] { Sp, Parenthesized(arg) })).ToArray());
    private static Formula Eqn(Formula left, Formula right) => Equal(left, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, body);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula Type => X("Type");
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula FinThree => Fin(D(3));
    private static Formula RealFamily => Arrow(X("A"), Arrow(R, R));
    private static Formula Mult => Arrow(FinThree, N);
    private static Formula Inst(Formula body) => Seq(OpenBracket,
        Call("Fintype", X("A")), CloseBracket, Sp, Comma, Sp, body);
    private static Formula Space(Formula m) => Parenthesized(Seq(Sigma, Sp,
        Parenthesized(Seq(X("j"), Sp, Colon, Sp, FinThree)), Sp, Comma, Sp,
        Fin(App(m, X("j")))));
    private static Formula MatrixOf(Formula space) => Call("Matrix", space, space, C);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(F.Sum, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp,
            Comma, Sp, body);
    private static Formula Rotation(Formula m, Formula t) =>
        App(Q("Matrix", "diagonal"), Seq(LambdaLower, Sp,
            Parenthesized(Seq(X("i"), Sp, Colon, Sp, Space(m))), Sp, Mapsto, Sp,
            App(Q("Complex", "exp"), Multiply(Q("Complex", "I"),
                Cast(Multiply(Subtract(Cast(Call("val", App(Q("Sigma", "fst"), X("i"))), R),
                    D(1)), t), C)))));
    private static Formula Probability => App(X("p"), X("a"), X("theta"));
    private static Formula Quantum(Formula p) => Call("QuantumSpinOne", p);
    private static Formula General(Formula p) => Call("RotationSpinOne", p);

    private static Formula QuantumDefinition() => All("A", Type, Inst(All("p", RealFamily,
        Eqn(Quantum(X("p")), Parenthesized(QuantumBody())))));

    private static Formula QuantumBody() => Ex("multiplicity", Mult,
        Ex("rho", Call("DensityState", Space(X("multiplicity"))),
            Ex("E", Arrow(X("A"), MatrixOf(Space(X("multiplicity")))),
                And(And(All("a", X("A"), App(Q("Matrix", "PosSemidef"), App(X("E"), X("a")))),
                    Eqn(Sum("a", X("A"), App(X("E"), X("a"))), D(1))),
                    All("a", X("A"), All("theta", R,
                        Eqn(App(Q("Matrix", "trace"),
                            Multiply(Multiply(Multiply(
                                Rotation(X("multiplicity"), X("theta")),
                                App(Q("CStarMatrix", "ofMatrix", "symm"), Call("val", X("rho")))),
                                App(Q("Matrix", "conjTranspose"),
                                    Rotation(X("multiplicity"), X("theta")))), App(X("E"), X("a")))),
                            Cast(Probability, C))))))));

    private static Formula FourierBody() =>
        Add(Add(Add(Add(App(X("cZero"), X("a")),
            Multiply(App(X("cOne"), X("a")), App(Q("Real", "cos"), X("theta")))),
            Multiply(App(X("sOne"), X("a")), App(Q("Real", "sin"), X("theta")))),
            Multiply(App(X("cTwo"), X("a")), App(Q("Real", "cos"), Multiply(D(2), X("theta"))))),
            Multiply(App(X("sTwo"), X("a")), App(Q("Real", "sin"), Multiply(D(2), X("theta")))));

    private static Formula RotationDefinitionBody() => All("A", Type, Inst(All("p", RealFamily,
        Eqn(General(X("p")),
            And(Ex("cZero", Arrow(X("A"), R), Ex("cOne", Arrow(X("A"), R),
                Ex("sOne", Arrow(X("A"), R), Ex("cTwo", Arrow(X("A"), R),
                    Ex("sTwo", Arrow(X("A"), R), All("a", X("A"), All("theta", R,
                        Eqn(Probability, FourierBody())))))))),
                And(All("a", X("A"), All("theta", R,
                    And(new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, Probability),
                        new Formula.Relation(Probability, FormulaRelationOperator.LessThanOrEqual, D(1))))),
                    All("theta", R, Eqn(Sum("a", X("A"), Probability), D(1)))))))));

    private static Formula ClaimBody() => All("A", Type, Inst(
        new Formula.Logic(new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual,
            App(Q("Fintype", "card"), X("A"))), FormulaLogicOperator.Implies,
            All("p", RealFamily, IffOf(Quantum(X("p")), General(X("p")))))));
}
