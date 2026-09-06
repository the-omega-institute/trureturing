using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintFiniteMaximumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintFiniteMaximum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constrained second variation is exactly the maximum of the thirty-two branch forms.",
        H("Ququint Finite Sign Maximum"),
        Blocks(
            Claim("signPattern", "The five bits of a branch",
                Seq(Forall, Sp, S, Colon, Fin32, Comma, Forall, Sp, I, Colon, Fin5, Comma,
                    Call(Name("signPattern"), S, I), Eq,
                    Call(Name("decide"), NotEqual(BranchBit, D(0)))),
                "signPattern returns Bool. Nat.div is natural-number quotient and Nat.mod is remainder; "
                    + "the exponent uses natural subtraction. Index zero selects the highest of the five bits.",
                DescribeRole.Definition),
            Claim("signValue", "The real sign coefficient",
                Seq(Forall, Sp, S, Colon, Fin32, Comma, Forall, Sp, I, Colon, Fin5, Comma,
                    Call(Name("signValue"), S, I), Eq,
                    Call(Name("ite"), Call(Name("signPattern"), S, I), D(1), Seq(Minus, D(1)))),
                "The real coefficient is one when the Boolean signPattern is true and minus one otherwise.",
                DescribeRole.Definition),
            Claim("integerWitness", "The complete integer witness table",
                Seq(Name("integerWitness"), Colon, Fin32, To,
                    Parenthesized(Seq(Name("Fin"), Sp, D(4), To, Mathbb, Grp(F.Id("Z")))), Comma,
                    Forall, Sp, S, Colon, Fin32, Comma, Call(Name("integerWitness"), S), Eq, Call(WitnessTable, S)),
                "The outer vector is indexed by s in Fin 32, starting at zero, and each row by Fin 4. "
                    + "These are all thirty-two integer cases in the Lean definition; its default case is the last row, "
                    + "because the input lies in Fin 32.", DescribeRole.Definition),
            Claim("secondVariation", "The second variation expression",
                Seq(Forall, Sp, V, Colon, Geo("State"), Comma,
                    Call(Name("secondVariation"), V), Eq, Variation(V)),
                "This definition includes the signed nonzero contribution, the five absolute values, "
                    + "and the subtracted squared norm term.", DescribeRole.Definition),
            Claim("branchMaximum", "The finite maximum",
                Seq(Forall, Sp, A, Colon, Coordinates, Comma,
                    Call(Name("branchMaximum"), A), Eq, Maximum(A)),
                "The maximum is Finset.univ.sup' over the nonempty finite type Fin 32.",
                DescribeRole.Definition),
            Claim("branch_eval", "Evaluation of each branch",
                Seq(Forall, Sp, S, Colon, Fin32, Comma, Forall, Sp, A, Colon, Coordinates, Comma,
                    Quadratic(Call(Data("branch"), S), A), Eq, Quadratic(Data("base"), A), Plus,
                    Sum, Underscore, Grp(Seq(I, Colon, Fin5)),
                    Call(Name("signValue"), S, I), Cdot, Quadratic(Call(Data("zeroQ"), I), A)),
                "The coefficient signValue is one for a set bit and minus one for an unset bit, "
                    + "using the same most-significant-bit-first order as branch."),
            Claim("secondVariation_coordinates", "The absolute values in tangent coordinates",
                Seq(Forall, Sp, A, Colon, Coordinates, Comma,
                    Call(Name("secondVariation"), Tangent(A)), Eq, Quadratic(Data("base"), A), Plus,
                    Sum, Underscore, Grp(Seq(I, Colon, Fin5)),
                    Call(Name("abs"), Quadratic(Call(Data("zeroQ"), I), A))),
                "The bridge evaluates base, zeroQ and gram on the actual tangent vector."),
            Claim("finite_sign_maximum", "Exact sign maximum in coordinates",
                Seq(Forall, Sp, A, Colon, Coordinates, Comma, Variation(Tangent(A)), Eq, Maximum(A)),
                "For each real coordinate vector, choose the five signs of its zero-point values. "
                    + "The resulting branch equals the sum of absolute values; every other branch is at most it."),
            Claim("finite_sign_maximum_tangent", "Exact sign maximum on the tangent subspace",
                Seq(Forall, Sp, V, Colon, Geo("tangent"), Comma,
                    Variation(StateValue(V)), Eq, Maximum(CoordinatesOf(V))),
                "The inverse of tangentEquiv supplies the coordinates of every tangent vector."),
            Claim("negativity_iff", "Both directions of negative definiteness",
                Seq(Parenthesized(Seq( Forall, Sp, V, Colon, Geo("tangent"), Comma,
                    V, Neq, D(0), Implies, Call(Name("secondVariation"), StateValue(V)), Lt, D(0))),
                    Iff, Parenthesized(Seq( Forall, Sp, S, Colon, Fin32, Comma,
                    Call(Seq(Name("Matrix"), Dot, Name("PosDef")),
                        Seq(Minus, Call(Data("branch"), S)))))),
                "Necessity bounds each branch by the strictly negative maximum. Sufficiency uses "
                    + "the finite-maximum strict inequality criterion. Symmetry is proved independently "
                    + "of the LDL certificates. The integer attainability clause is also checked below; "
                    + "it is not needed to infer either direction from the exact maximum identity."),
            Claim("second_variation_negative", "Strict negativity for this ququint state",
                Seq(Forall, Sp, V, Colon, Geo("tangent"), Comma, V, Neq, D(0), Implies,
                    Call(Name("secondVariation"), StateValue(V)), Lt, D(0)),
                "The implication from the criterion consumes all_branches_negative, so all thirty-two "
                    + "LDL conclusions are on the live proof path to strict negativity."),
            Claim("integerWitness_signs", "The explicit integer witnesses have all required signs",
                Seq(Forall, Sp, S, Colon, Fin32, Comma, Forall, Sp, I, Colon, Fin5, Comma,
                    D(0), Lt, Call(Name("signValue"), S, I), Cdot,
                    Quadratic(Call(Data("zeroQ"), I), Witness(S))),
                "integerWitness is the explicit thirty-two-case integer table in Lean. All 160 "
                    + "strict sign inequalities follow from rational bounds for the positive radical "
                    + "and its square and cube; no floating-point result is trusted."),
            Claim("sign_patterns_attained", "Every sign pattern is attained with integer coordinates",
                Seq(Forall, Sp, S, Colon, Fin32, Comma, Exists, Sp, A, Colon, Coordinates, Comma,
                    Parenthesized(Seq( Forall, Sp, J, Colon, Name("Fin"), Sp, D(4), Comma,
                    Exists, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("Z")), Comma,
                    Call(A, J), Eq, Parenthesized(Seq( F.Id("n"), Colon, RealType)))),
                    Sp, Land, Sp, A, Neq, D(0), Sp, Land, Sp,
                    Parenthesized(Seq(Forall, Sp, I, Colon, Fin5, Comma,
                    D(0), Lt, Call(Name("signValue"), S, I), Cdot,
                    Wigner(Tangent(A), Call(Bridge("zeroIndex"), I))))),
                "The same witnesses are nonzero and lie in the actual tangent subspace through tangentEquiv. "
                    + "Positive signValue times Wigner value certifies the requested strict sign."),
            Paragraph(Text("QuquintStrictDecrease consumes the negative second variation to prove the "
                + "normalized exact change and strict decrease of lOne and log lOne. This result concerns only the specified "
                + "ququint state and constrained tangent family; it makes no claim about other "
                + "dimensions, other critical points, general mana extremisation, author-verbatim "
                + "Claim C, or global novelty.")))));

    private static DocumentBlock Claim(string name, string title, Formula statement, string explanation,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("ququint-maximum-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula Variation(Formula v) => Seq(Parenthesized(Seq(
        new Formula.Subscript(Sum, new Formula.Relation(QP, FormulaRelationOperator.MemberOf,
            Parenthesized(Seq(Name("Finset"), Dot, Name("univ"), Setminus, Geo("zeroPoints"))))),
        Parenthesized(Seq( Call(Seq(Name("SignType"), Dot, Name("sign")), Wigner(Geo("psi"), QP)),
        Colon, RealType)), Cdot, Wigner(v, QP))), Plus, Parenthesized(Seq(
        new Formula.Subscript(Sum, new Formula.Relation(QP, FormulaRelationOperator.MemberOf, Geo("zeroPoints"))),
        Call(Name("abs"), Wigner(v, QP)))), Minus,
        Call(Geo("lOne"), Geo("psi")), Cdot,
        Call(Seq(Name("Norm"), Dot, Name("norm")), v), Caret, Grp(D(2)));
    private static Formula Maximum(Formula a) => Seq(Name("max"), Underscore,
        Grp(Seq(S, Colon, Fin32)), Quadratic(Call(Data("branch"), S), a));
    private static Formula Quadratic(Formula m, Formula a) =>
        Call(Name("dotProduct"), a, Call(Seq(Name("Matrix"), Dot, Name("mulVec")), m, a));
    private static Formula Wigner(Formula v, Formula qp) => Call(Geo("wigner"), v,
        Seq(Parenthesized(Seq( qp)), Dot, D(1)), Seq(Parenthesized(Seq( qp)), Dot, D(2)));
    private static Formula StateValue(Formula v) => Seq(Parenthesized(Seq( v, Colon, Geo("State"))));
    private static Formula Tangent(Formula a) => StateValue(Call(Geo("tangentEquiv"), a));
    private static Formula CoordinatesOf(Formula v) =>
        Call(Seq(Geo("tangentEquiv"), Dot, Name("symm")), v);
    private static Formula Witness(Formula s) => Seq(Parenthesized(Seq( Parenthesized(Seq( J, Colon, Name("Fin"), Sp,
        D(4))), Mapsto, Parenthesized(Seq( Call(Name("integerWitness"), s, J), Colon, RealType)))));
    private static Formula BranchBit => Call(Seq(Name("Nat"), Dot, Name("mod")),
        Call(Seq(Name("Nat"), Dot, Name("div")), Call(Name("val"), S),
            Seq(D(2), Caret, Grp(Seq(D(4), Minus, Call(Name("val"), I))))), D(2));
    private static Formula WitnessTable => Vector(
        IntegerRow(-4, 0, 4, 1), IntegerRow(-3, 4, -1, 4), IntegerRow(-4, -1, -2, 4), IntegerRow(-4, 2, -1, 3),
        IntegerRow(-4, -1, 0, 4), IntegerRow(-2, -3, -4, 4), IntegerRow(-4, -3, -2, 4), IntegerRow(-3, 4, 4, -2),
        IntegerRow(-4, -4, 4, -4), IntegerRow(-3, -4, 3, -4), IntegerRow(-4, -3, 4, -3), IntegerRow(-4, 2, 1, 1),
        IntegerRow(-4, -3, 4, -4), IntegerRow(-4, -4, 3, -4), IntegerRow(-4, -2, 2, -1), IntegerRow(-4, -3, 3, -3),
        IntegerRow(-3, -1, -4, 2), IntegerRow(-4, -3, -4, 3), IntegerRow(-4, -1, -4, 4), IntegerRow(-4, -2, -4, 4),
        IntegerRow(-4, -4, -4, -4), IntegerRow(-4, -4, -4, -1), IntegerRow(-4, -4, -2, 4), IntegerRow(-4, -4, -4, 3),
        IntegerRow(-3, -4, 4, -4), IntegerRow(-2, -4, 1, -3), IntegerRow(-4, -4, 4, -3), IntegerRow(-4, 1, -2, 2),
        IntegerRow(-4, -4, -2, -4), IntegerRow(-4, -4, -2, -3), IntegerRow(-4, -4, 0, 1), IntegerRow(-4, -4, -1, 1));
    private static Formula IntegerRow(params int[] entries) => Vector(entries.Select(n => n < 0 ? new Formula.Negate(Num(-n)) : Num(n)).ToArray());
    private static Formula Vector(params Formula[] entries) => Seq(OpenBracket, JoinWithComma(entries), CloseBracket);
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(JoinWithComma(args)));
    private static Formula JoinWithComma(Formula[] args) =>
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray());
    private static Formula A => F.Id("a");
    private static Formula V => F.Id("v");
    private static Formula S => F.Id("s");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula QP => F.Id("qp");
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Coordinates => Seq(Parenthesized(Seq( Name("Fin"), Sp, D(4), To, RealType)));
    private static Formula Fin32 => Seq(Name("Fin"), Sp, D(3, 2));
    private static Formula Fin5 => Seq(Name("Fin"), Sp, D(5));
    private static Formula Geo(string name) => Qualified("QuquintWignerCriticalGeometry", name);
    private static Formula Data(string name) => Qualified("QuquintCertificateData", name);
    private static Formula Bridge(string name) => Qualified("QuquintCertificateBridge", name);
    private static Formula Qualified(string module, string name) => Seq(Name("D5"), Dot,
        Name("S3"), Dot, Name("Quantum"), Dot, Name("Magic"), Dot, Name(module), Dot, Name(name));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
