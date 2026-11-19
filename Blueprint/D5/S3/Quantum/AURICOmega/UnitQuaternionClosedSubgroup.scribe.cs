using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class UnitQuaternionClosedSubgroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined, for every positive tolerance, by a chain of elements of the subgroup with consecutive readings of the quaternion comparison model within that tolerance of one, is the whole group.",
        H("Closed chain-connected subgroups of the unit quaternions"),
        Blocks(
            Node("eq-top", "eq_top_of_isClosed_of_chainConnected",
                "A closed, chain-connected, noncommutative subgroup is the whole group",
                StatementSource.FromAuthor(EqTopFormula()), DescribeRole.Theorem,
                "Here unitary(H[R]) is the group of unit quaternions, IsClosed(H) says that H is closed as a subset of it, top is the whole group, "
                    + "and kappa(quaternionModel, a, b) = (1 + <a, b>) / 2 is the reading of the quaternion comparison model, with <a, b> the real inner product of quaternions. "
                    + "The second hypothesis says that for every e > 0 any two elements of H are joined by a finite chain of elements of H whose consecutive readings exceed 1 - e. "
                    + "Without the noncommutativity hypothesis the conclusion fails, because the trivial subgroup is closed, as a one-element subset, and satisfies the chain condition, as every chain in it is trivial; this consequence is not among the formal statements of the module. "
                    + "The statement is classical: a closed subgroup is compact, the reading is 1 - |x - y|^2 / 4, so the chain condition says that any two elements are joined inside H by chains with arbitrarily small steps, and for a compact metric space this is equivalent to connectedness; hence the statement is the fact that a closed connected nonabelian subgroup of the unit quaternions, the group SU(2), is the whole group, and the argument below is elementary and uses no Lie theory; this equivalence and this classical fact are not among the formal statements of the module. "
                    + "Small elements. Since H contains two elements that do not commute, it contains an element other than 1, and for every e > 0 a chain in H from 1 to that element has a step from 1 to an element b of H different from 1 with kappa(1, b) > 1 - e. "
                    + "As kappa(1, b) = (1 + re b) / 2, the subgroup H contains elements h_k different from 1 whose real parts tend to 1. "
                    + "A limiting axis and a full circle. Write h_k = cos t_k + sin t_k * n_k with t_k = arccos(re h_k) and n_k a unit imaginary quaternion; the angles t_k are positive and tend to 0. "
                    + "By compactness of the unit sphere of imaginary quaternions a subsequence of the n_k converges to a unit imaginary quaternion a. "
                    + "For t >= 0, de Moivre's formula writes the power of h_k with exponent m_k, the integer part of t / t_k, as cos(m_k t_k) + sin(m_k t_k) * n_k, and m_k t_k tends to t, so along the subsequence these powers converge to cos t + sin t * a. "
                    + "As H is closed, it contains cos t + sin t * a for every t >= 0, and, taking inverses, for every real t. "
                    + "Call a unit imaginary quaternion with this property an axis of H. "
                    + "A second axis. Let n be the axis just found. The unit imaginary quaternions n and i have the same reading against 1, so by two-point homogeneity some unit quaternion p satisfies p * n * p^-1 = i, and conjugation by p serves as coordinates in which n is i. "
                    + "Quaternions commuting with i are those with vanishing j and k coordinates, so quaternions commuting with n commute with each other, and since H is noncommutative some element of H does not commute with n. "
                    + "Along a chain in H from 1 to that element with consecutive readings above 1/2 there are consecutive elements c and d with c commuting with n and d not; then g = c^-1 * d lies in H, does not commute with n, and kappa(1, g) = kappa(c, d) > 1/2; the conjugate p * g * p^-1 has the same reading against 1, so it has positive real part, and it does not commute with i. "
                    + "Conjugating an axis by an element of H gives an axis, so g * n * g^-1 is an axis; its image under conjugation by p is the conjugate of i by p * g * p^-1, and because p * g * p^-1 has positive real part and does not commute with i, the i coordinate of that image has square less than 1, so this axis is neither n nor -n. "
                    + "All axes, by rotating axes about one another. The negative of an axis is an axis, and conjugating an axis b by cos s + sin s * a, with a an axis, gives an axis. "
                    + "In the coordinates where n is i, conjugating i by cos s + sin s * a, where a has i coordinate h with h^2 < 1, reaches every i coordinate in the interval from 2 h^2 - 1 to 1. "
                    + "Starting from the second axis, taken with nonnegative i coordinate h0 < 1, each such step either reaches the i coordinate 0 or lowers the i coordinate by at least 1 - h0 while keeping it nonnegative, so after finitely many steps some axis has i coordinate 0. "
                    + "Conjugating i by cos s + sin s * a, with a that axis, gives axes of every i coordinate between -1 and 1, and conjugation by cos s + sin s * i moves an axis along its circle of constant i coordinate to every point of that circle, so every unit imaginary quaternion is an axis of H. "
                    + "Polar form. Every unit quaternion u equals cos t + sin t * m with t = arccos(re u) and m a unit imaginary quaternion; since m is an axis of H, u lies in H, and H is the whole group."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("unit-quaternion-closed-subgroup-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Top => Seq(Operatorname, Grp(F.Id("top")));
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);

    private static Formula EqTopFormula()
    {
        Formula h = F.Id("H"), e = F.Id("e"), x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula step = Seq(LambdaLower, Sp, a, Sp, b, Dot, Sp,
            And(Rel(b, FormulaRelationOperator.MemberOf, h),
                Rel(Sub(D(1), e), FormulaRelationOperator.LessThan, Kappa(a, b))));
        Formula chain = ForAll("e", Reals, Implies(Rel(D(0), FormulaRelationOperator.LessThan, e),
            ForAllMany(h, Call("ReflTransGen", step, x, y), "x", "y")));
        Formula noncommutative = ExistsMany(h,
            Rel(Mul(x, y), FormulaRelationOperator.NotEqual, Mul(y, x)), "x", "y");
        return Disp(ForAll("H", Call("Subgroup", Units),
            Implies(Call("IsClosed", h), Implies(chain, Implies(noncommutative, Equal(h, Top))))));
    }
}
