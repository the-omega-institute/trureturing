using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class LossyQubitPartialJMTightnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/lobo2026generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial joint measurability bounds the efficiency of two lossy projective qubit measurements.",
        H("Lossy Qubit Partial Joint-Measurability Tightness"), Blocks(
            Node("effects", "Lossy measurement effects",
                "Equation (13) multiplies each conclusive projector by the efficiency eta and assigns the remaining weight to the identity. The matrix blochMatrix 1 r is the projector (I + r dot sigma)/2 for a unit Bloch vector r. Outcomes zero and one correspond to the positive and negative Bloch directions; outcome two is the no-click outcome. Inputs zero and one select the two measurements.",
                DescribeRole.Definition, EffectsFormula(), AssessedProvenance.FromLiterature(Source)),
            Node("G", "The outcomes to be determined",
                "In case (d), both conclusive outcomes of the first input must be determined, and no outcome of the second input is constrained. The indices here start at zero.",
                DescribeRole.Definition, All("y", Fin(2), Equal(Call("G", X("y")),
                    Call("ite", Equal(X("y"), Typed(Num(0), Fin(2))),
                        Seq(OpenBrace, Num(0), Comma, Sp, Num(1), CloseBrace),
                        Typed(Emptyset, Call("Finset", Fin(3)))))),
                AssessedProvenance.FromLiterature(Source)),
            Node("starPart", "The positive conclusive remainder",
                "Definition 2 defines the starred operator by subtracting from the common marginal the effects whose outcomes lie in the complement of G at that input. The complement is taken in Fin 3. Its positivity is a separate condition in GJointMeasurable.",
                DescribeRole.Definition, All("E", PartialParents(), All("W", Marginals(),
                    All("beta", Fin(2), All("y", Fin(2),
                        Equal(Call("starPart", X("E"), X("W"), X("beta"), X("y")),
                            Subtract(At(X("W"), X("beta")), SumWhere("b", Complement(),
                                At(X("E"), X("beta"), X("b"), X("y"))))))))),
                AssessedProvenance.FromLiterature(Source)),
            Node("GJointMeasurable", "Partial joint measurability",
                "Definition 2 requires a POVM for each input, common marginals across inputs, agreement with the lossy effects, and positive starred operators. For each outcome in G, only the branch whose binary label equals that outcome can contribute, and its effect equals the starred operator. The binary label embeds into Fin 3 by Fin.castSucc.",
                DescribeRole.Definition, All("eta", Reals(), All("r", Vectors(),
                    Equivalence(Call("GJointMeasurable", X("eta"), X("r")),
                        Ex("E", PartialParents(), Ex("W", Marginals(), JointConditions()))))),
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The efficiency bound",
                "For any two unit Bloch vectors and any efficiency between zero and one, partial joint measurability implies eta times (2 plus the Euclidean norm of their cross product) is at most 2. Mathlib's crossProduct acts on coordinate functions, and WithLp.toLp 2 equips its value with the Euclidean norm. For unit vectors this norm is the sine of their angle, and hence also the sine of the acute angle between the unoriented axes. This is the necessity direction of the threshold in Eq. (36).",
                DescribeRole.Definition, Equivalence(X("claim"), Claim()),
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Necessity of the threshold",
                "Write a Hermitian operator as a scalar multiple of the identity plus v dot sigma, so v is its vector of Pauli coefficients. A positive qubit operator dominated by a rank-one projector is a multiple of that projector. At the second input, the conclusive coefficient vectors are therefore parallel to its axis. The coefficient vector of the difference of the two no-click effects has norm at most 1 minus eta at either input. Comparing the common marginal difference across inputs and taking its cross product with the second axis gives eta times the cross-product norm at most twice (1 minus eta). This proves the asserted bound for every axis pair. The source gives the complementary sufficient construction and reports numerical evidence of tightness; the statement here proves necessity exactly.",
                DescribeRole.Theorem, X("claim"), AssessedProvenance.FromRepo(Source))
        ), []));

    private static Formula EffectsFormula() => All("eta", Reals(), All("r", Vectors(),
        All("b", Fin(3), All("y", Fin(2), Equal(Call("effects", X("eta"), X("r"), X("b"), X("y")),
            Call("ite", Equal(X("b"), Typed(Num(2), Fin(3))),
                Smul(Subtract(Num(1), X("eta")), Typed(Num(1), X("QubitMatrix"))),
                Smul(X("eta"), At(Qualified("ActualPureQubitCostInfimum", "blochMatrix"), Num(1), Call("ite", Equal(X("b"), Typed(Num(0), Fin(3))),
                    At(X("r"), X("y")), Negate(At(X("r"), X("y"))))))))))));

    private static Formula JointConditions() => And(
        All("y", Fin(2), At(Qualified("ConcealmentKernelNecessityRefutation", "IsPOVM"),
            LambdaOf("k", Outcomes(), At(X("E"), At(Qualified("Prod", "fst"), X("k")),
                At(Qualified("Prod", "snd"), X("k")), X("y"))))), And(
        All("beta", Fin(2), All("y", Fin(2), Equal(
            SumOver("b", Fin(3), At(X("E"), X("beta"), X("b"), X("y"))),
            At(X("W"), X("beta"))))), And(
        All("b", Fin(3), All("y", Fin(2), Equal(Call("effects", X("eta"), X("r"), X("b"), X("y")),
            SumOver("beta", Fin(2), At(X("E"), X("beta"), X("b"), X("y")))))), And(
        All("beta", Fin(2), All("y", Fin(2), At(Qualified("Matrix", "PosSemidef"), Starred()))),
        All("beta", Fin(2), All("y", Fin(2), All("b", Fin(3), Implication(
            Member(X("b"), Call("G", X("y"))),
            Equal(At(X("E"), X("beta"), X("b"), X("y")), Call("ite",
                Equal(X("b"), At(Qualified("Fin", "castSucc"), X("beta"))),
                Starred(), Typed(Num(0), X("QubitMatrix"))))))))))));

    private static Formula Starred() => Call("starPart", X("E"), X("W"), X("beta"), X("y"));
    private static Formula Complement() => At(Qualified("Finset", "filter"),
        LambdaOf("b", Fin(3), new Formula.Not(Parenthesized(Member(X("b"), Call("G", X("y")))))),
        Typed(Qualified("Finset", "univ"), Call("Finset", Fin(3))));
    private static Formula Claim() => All("r", BlochSpace(), All("s", BlochSpace(), All("eta", Reals(),
        Implication(Equal(Norm(X("r")), Num(1)), Implication(Equal(Norm(X("s")), Num(1)),
        Implication(LE(Num(0), X("eta")), Implication(LE(X("eta"), Num(1)),
        Implication(Call("GJointMeasurable", X("eta"), Seq(Bang, OpenBracket, X("r"), Comma, Sp, X("s"), CloseBracket)),
            LE(Multiply(X("eta"), Parenthesized(Add(Num(2), Norm(
                At(Qualified("WithLp", "toLp"), Num(2), Call("crossProduct",
                    At(Qualified("WithLp", "ofLp"), X("r")),
                    At(Qualified("WithLp", "ofLp"), X("s")))))))), Num(2))))))))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        Formula formula, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
        name == "result" ? new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("lobo-balanzo-juando-pironio-2026-eq36-tightness"),
            ResolutionKind.Proved) : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Outcomes() => Seq(Fin(2), Sp, Times, Sp, Fin(3));
    private static Formula BlochSpace() => Call("EuclideanSpace", Reals(), Fin(3));
    private static Formula Vectors() => Arrow(Fin(2), BlochSpace());
    private static Formula Marginals() => Arrow(Fin(2), X("QubitMatrix"));
    private static Formula PartialParents() => Arrow(Fin(2), Arrow(Fin(3), Marginals()));
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula LambdaOf(string v, Formula domain, Formula body) =>
        Parenthesized(Seq(Typed(X(v), domain), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implication(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula SumOver(string v, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(v), domain)), Sp, Parenthesized(body));
    private static Formula SumWhere(string v, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(X(v), set)), Sp, Parenthesized(body));
}
