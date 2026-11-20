using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class ProjectiveQuaternionModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unit quaternions modulo sign, with transfer x * y^-1 * z and reading <x, y>^2, form a noncommutative, chain-connected, reading-complete ternary comparison structure touching zero whose reading has feature rank r exactly when r >= 10, and in which every point has two distinct points of reading zero.",
        H("The unit quaternions modulo sign as a ternary comparison structure"),
        Blocks(
            Node("sign-subgroup", "signSubgroup", "The sign subgroup",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "signSubgroup is the subgroup of the group of unit quaternions whose elements are exactly 1 and -1. "
                    + "It contains 1, and it is closed under products and inverses because (-1) * (-1) = 1 and (-1)^-1 = -1."),
            Node("sign-subgroup-normal", "signSubgroup_normal", "The sign subgroup is normal",
                StatementSource.FromAuthor(Disp(Call("Normal", SignSubgroup))), DescribeRole.Definition,
                "The subgroup signSubgroup is normal: for g a unit quaternion, g * 1 * g^-1 = 1 and g * (-1) * g^-1 = -1, since -1 is central in the quaternions."),
            Node("projective-quaternion", "ProjectiveQuaternion", "Unit quaternions modulo sign",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "ProjectiveQuaternion is the quotient group of the unit quaternions by the normal subgroup signSubgroup. "
                    + "Two unit quaternions x and y have the same class exactly when x^-1 * y is 1 or -1, that is, when y = x or y = -x. "
                    + "Classically, the unit quaternions modulo sign are the rotation group of Euclidean three-space, through the action q acting by v mapsto q * v * q^-1 on the imaginary quaternions; this identification is a remark only and is not part of the definition."),
            Node("projective-model", "projectiveModel", "The structure on unit quaternions modulo sign",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "projectiveModel is the ternary comparison structure on ProjectiveQuaternion whose transfer is tri x y z = x * y^-1 * z, computed in the quotient group, and whose reading kappa of the classes of unit quaternions x and y is <x, y>^2, where <x, y> = re x * re y + imI x * imI y + imJ x * imJ y + imK x * imK y is the real inner product of the quaternions. "
                    + "The reading is well defined because changing the sign of either representative changes the sign of <x, y> and leaves its square unchanged. "
                    + "The transfer identities are group identities. The reading is symmetric and nonnegative. "
                    + "It equals one exactly when the two classes agree: two unit vectors satisfy <x, y>^2 = 1 only when <x, y> = 1 or <x, y> = -1, that is, when y = x or y = -x. "
                    + "Multiplication on the right by u^-1 * v and on the left by u * v^-1 preserves the inner product of unit quaternions, which gives the two invariance laws of the reading under transfer. "
                    + "The Gram forms are nonnegative because the reading is the inner product of the feature vectors described with the theorem below, so each Gram form is the squared norm of a combination of feature vectors."),
            Node("feature-rank-ten", "projectiveModel_featureRank_ten", "Feature rank ten and the remaining properties",
                StatementSource.FromAuthor(MainFormula()), DescribeRole.Theorem,
                "Noncommutativity: take the classes of i, 1 and r = (3 + 4 j) / 5. Then tri i 1 r = i * r and tri r 1 i = r * i, and the unit quaternions i * r and r * i have inner product -7 / 25, which is neither 1 nor -1, so their classes differ. "
                    + "Chain connectedness: the unit-quaternion structure with reading (1 + <a, b>) / 2 is chain connected. A step with 1 - e / 4 < (1 + <a, b>) / 2 gives 1 - e / 2 < <a, b>, and since t^2 >= 2 t - 1 for every real t, it gives 1 - e < <a, b>^2; so a chain of unit quaternions for e / 4 maps to a chain of classes for e. "
                    + "Touching zero: the classes of 1 and i have reading <1, i>^2 = 0. "
                    + "Reading completeness: for a sequence of classes whose readings with each other tend to one, choose representatives on the unit sphere of the quaternions. The sphere is compact, so a subsequence of representatives converges to a unit quaternion a; for each fixed n the readings of the n-th class with the subsequence converge to the reading of the n-th class with the class of a, so the readings of the sequence with the class of a tend to one. "
                    + "Feature rank ten: the map q mapsto (re q^2, imI q^2, imJ q^2, imK q^2, sqrt 2 * q_a * q_b for the six pairs a < b) into Euclidean ten-space, applied to a representative, satisfies <f(p), f(q)> = <p, q>^2, because the square of a sum of four products expands into the four squared products and twice the six cross products. "
                    + "No feature rank nine: suppose the reading is the Gram kernel of a map g into Euclidean nine-space. Take the ten unit quaternions t_1, ..., t_10 given by 1, i, j, k and (3 e_a + 4 e_b) / 5 for the six pairs a < b of the basis e_1, ..., e_4 = 1, i, j, k. If the combination sum_a c_a g(t_a) vanishes, its inner products with the vectors g(t_b) give the ten linear equations sum_a c_a <t_a, t_b>^2 = 0 in the ten unknowns c_a, and solving this system explicitly gives c = 0. "
                    + "Conceptually, the only quadratic form vanishing at all ten points is zero: a form vanishing at 1, i, j and k has zero diagonal coefficients, and its value at (3 e_a + 4 e_b) / 5 is then 12 / 25 times its coefficient of y_a y_b. Hence the ten squared linear forms <t_a, y>^2 form a basis of the ten-dimensional space of quadratic forms in y, and the matrix of the system is invertible. "
                    + "So the ten vectors g(t_a) are linearly independent, which is impossible in a space of dimension nine. "
                    + "Exact feature ranks: HasFeatureRank(projectiveModel, r) asserts a realization of the reading as the Gram kernel of a map into Euclidean r-space, and it is equivalent to the bound r on the rank of every finite Gram matrix of the reading, by gramRankLE_iff_hasFeatureRank; a rank bound r is a rank bound for every s >= r, so feature rank is monotone in the dimension. "
                    + "Hence feature rank ten gives feature rank r for every r >= 10, and feature rank r for some r <= 9 would give feature rank nine; so the reading has feature rank r exactly when 10 <= r, and ten is its least feature rank. "
                    + "Two points of reading zero: for every unit quaternion x, left multiplication by x preserves the inner product, so the readings of x with x * i and x * j are <1, i>^2 = 0 and <1, j>^2 = 0, and the classes of x * i and x * j differ because their reading is <i, j>^2 = 0 rather than one. "
                    + "In particular the reading does not have feature rank five. "
                    + "Thus the structure is noncommutative, chain connected, touches zero and has complete reading, which are all the qualitative hypotheses under which a structure of feature rank five is isomorphic to the unit-quaternion structure; the two structures are separated by their least feature ranks, ten here against five there. "
                    + "In the unit-quaternion structure the only point of reading zero with x is -x, while here every point has at least two distinct points of reading zero. "
                    + "The number ten is the dimension of the space of quadratic forms in four variables, the classical dimension of the symmetric square of a four-dimensional space; its decomposition as 1 + 9, the constants together with the matrix coefficients of the three-dimensional rotation representation, is also classical. The theorem is a statement about this one explicit structure; the count is not claimed as new."))));

    private static Formula Model => Seq(Operatorname, Grp(F.Id("projectiveModel")));
    private static Formula SignSubgroup => Seq(Operatorname, Grp(F.Id("signSubgroup")));
    private static Formula Carrier => Seq(Operatorname, Grp(F.Id("ProjectiveQuaternion")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);

    private static Formula MainFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula zeros = ForAll("p", Carrier, ExistsMany(Carrier,
            And(Rel(a, FormulaRelationOperator.NotEqual, b),
                And(Equal(Kappa(p, a), D(0)), Equal(Kappa(p, b), D(0)))), "a", "b"));
        return Disp(And(Call("Noncommutative", Model),
            And(Call("ChainConnected", Model),
                And(Call("TouchesZero", Model),
                    And(Call("ReadingComplete", Model),
                        And(ForAll("r", Naturals, Logic(Call("HasFeatureRank", Model, F.Id("r")),
                                FormulaLogicOperator.Iff, Rel(D(1, 0), FormulaRelationOperator.LessThanOrEqual, F.Id("r")))),
                            zeros))))));
    }

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("projective-quaternion-model-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
