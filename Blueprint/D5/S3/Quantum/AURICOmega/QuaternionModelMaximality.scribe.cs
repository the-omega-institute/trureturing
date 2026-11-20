using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionModelMaximalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ternary comparison structure of feature rank at most eight that contains a transfer- and reading-preserving copy of the unit quaternion comparison model is that copy, eight is the largest rank with this property, and in feature rank five a reading-preserving copy alone already exhausts the structure.",
        H("Maximality of the unit quaternion comparison model in small feature rank"),
        Blocks(
            Node("le-eight", "bijective_of_hasFeatureRank_le_eight", "A copy of the model in feature rank at most eight is everything",
                StatementSource.FromAuthor(LeEightFormula()),
                "Let C be a ternary comparison structure on M whose reading is the Gram kernel of a map into Euclidean r-space with r <= 8, and let j be a map from the unit quaternions into M that carries the transfer x * y^-1 * z of the model to the transfer of C and preserves the reading. Then j is a bijection. "
                    + "A preserved reading makes j injective, since reading one characterizes equality. "
                    + "For a point m of M, the readings kappa(C, j(y), m) form a one-point extension of the quaternion reading with self-reading one, so by the classification of one-point extensions they are (a + <b, y>) / sqrt 2 with a^2 + |b|^2 <= 1. "
                    + "Transfer preservation and the invariance laws of the reading show that the right translate x -> tri(C, m, j(1), j(x)) of the copy reads (a + <b * x, y>) / sqrt 2 against j(y). "
                    + "For e = 1, i, j and k, the differences of the features of the translate at e and at -e have the components orthogonal to all features of the copy pairwise orthogonal, with squared norm 2 - 4 * |b|^2. "
                    + "Together with the five orthogonal vectors formed from the features of the copy at 1 and -1 and at e and -e, they would be nine nonzero orthogonal vectors if |b|^2 < 1 / 2, which is impossible in dimension at most eight. "
                    + "Hence |b|^2 = 1 / 2; nonnegativity of the readings gives a = |b| = 1 / sqrt 2, and m has reading one with the image of the unit quaternion sqrt 2 * b, so m lies in the image of j. "
                    + "Neither noncommutativity, chain connectivity, touching zero nor completeness of the reading of C is assumed. "
                    + "Reading preservation cannot be dropped: a constant map preserves the transfer and is not injective. Whether transfer preservation can be dropped in feature rank six, seven or eight is not settled here; in feature rank five it can, as the last theorem shows.",
                DescribeRole.Theorem),
            Node("sharp", "forall_bijective_iff_le_eight", "Eight is the sharp rank",
                StatementSource.FromAuthor(SharpFormula()),
                "For a natural number r, every transfer- and reading-preserving copy of the unit quaternion comparison model inside a ternary comparison structure of feature rank r is a bijection exactly when r <= 8. "
                    + "For r <= 8 this is the previous theorem. "
                    + "For r >= 9, take two copies of the unit quaternions, M = unitary(H) x Bool, with transfer (x * y^-1 * z, a xor b xor c) and with the reading of the model within a layer and the reading one half between the layers. "
                    + "Its reading is the Gram kernel of the map into Euclidean nine-space sending (x, false) to (1, x, 0) / sqrt 2 and (x, true) to (1, 0, x) / sqrt 2, where x stands for the four quaternion coordinates and 0 for four zeros; so the structure has feature rank nine and hence every larger rank. "
                    + "The layer x -> (x, false) preserves transfer and reading and misses the second layer.",
                DescribeRole.Theorem),
            Node("rank-five", "bijective_of_hasFeatureRank_five_of_kappa", "In feature rank five a reading-preserving copy is everything",
                StatementSource.FromAuthor(RankFiveFormula()),
                "Let C be a ternary comparison structure on M of feature rank five and let j be a map from the unit quaternions into M that preserves the reading. Then j is a bijection; the transfer need not be preserved. "
                    + "For a point m, the translate x -> tri(C, m, j(1), j(x)) is again a reading-preserving copy and sends 1 to m. "
                    + "Each translate point reads (a + <b, y>) / sqrt 2 against j(y) with a^2 + |b|^2 = 1, by the classification of one-point extensions of feature rank five, and |b| <= a because the readings are nonnegative; so its readings against j(1) and j(-1) add up to sqrt 2 * a >= 1. "
                    + "These sums, as functions of x, form a one-point extension of feature rank five of the translated copy by the unit vector (phi(j(1)) + phi(j(-1))) / sqrt 2, where phi is the feature map of C; hence the sums at x and at -x add up to at most two, and the sum at x = 1, which belongs to m, equals one. "
                    + "For the readings of m this means 2 * a = sqrt 2 and |b|^2 = 1 / 2, so m has reading one with the image of the unit quaternion sqrt 2 * b and lies in the image of j.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("quaternion-model-maximality-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula AtMost(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula J => F.Id("j");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula TypeZero => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Copy => new Formula.TypeArrow(Units, M);

    /// <summary>j carries the transfer of the model to the transfer of C.</summary>
    private static Formula TransferPreserved()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        return ForAllMany(Units,
            Equal(At(J, Call("tri", Model, x, y, z)), Call("tri", C, At(J, x), At(J, y), At(J, z))),
            "x", "y", "z");
    }

    /// <summary>j carries the reading of the model to the reading of C.</summary>
    private static Formula ReadingPreserved()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return ForAllMany(Units,
            Equal(Call("kappa", C, At(J, x), At(J, y)), Call("kappa", Model, x, y)), "x", "y");
    }

    private static Formula Bijective => Call("Bijective", J);

    private static Formula LeEightFormula()
    {
        Formula r = F.Id("r");
        return Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M), ForAll("r", Naturals,
            Implies(Call("HasFeatureRank", C, r), Implies(AtMost(r, D(8)),
                ForAll("j", Copy, Implies(TransferPreserved(), Implies(ReadingPreserved(), Bijective)))))))));
    }

    private static Formula SharpFormula()
    {
        Formula r = F.Id("r");
        Formula every = ForAll("M", TypeZero, ForAll("C", Call("TernaryComparison", M), ForAll("j", Copy,
            Implies(Call("HasFeatureRank", C, r),
                Implies(TransferPreserved(), Implies(ReadingPreserved(), Bijective))))));
        return Disp(ForAll("r", Naturals, Iff(every, AtMost(r, D(8)))));
    }

    private static Formula RankFiveFormula() =>
        Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M),
            Implies(Call("HasFeatureRank", C, D(5)),
                ForAll("j", Copy, Implies(ReadingPreserved(), Bijective))))));
}
