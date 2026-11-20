using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonIsomorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noncommutative, chain-connected ternary comparison structure of feature rank five whose reading touches zero and is complete is in bijection with the unit quaternions, by a map that sends a chosen point to 1 and carries its transfer and reading to those of the quaternion comparison model.",
        H("Complete ternary comparison structures of feature rank five"),
        Blocks(
            Node("reading-complete", "ReadingComplete", "Complete reading",
                StatementSource.FromAuthor(ReadingCompleteFormula()), DescribeRole.Definition,
                "The reading of a ternary comparison structure C on M is complete when every sequence x of points of M whose readings kappa(C, x m, x n) exceed 1 - e for all m and n beyond some N, for every e > 0, has a point a whose readings kappa(C, x n, a) with the sequence exceed 1 - e for all n beyond some N, for every e > 0. "
                    + "Reading values close to one play the role of small distances, so this is completeness of M for the closeness measured by the reading. "
                    + "The condition holds for the quaternion comparison model, because its reading is one minus a quarter of the squared distance, 1 - |x - y|^2 / 4, and the unit quaternions are a closed subset of the complete space of quaternions; this consequence is not among the formal statements of the module."),
            Node("kappa-distance", "kappa_eq_one_sub_dist_sq", "The quaternion reading in terms of distance",
                StatementSource.FromAuthor(DistanceFormula()), DescribeRole.Lemma,
                "For unit quaternions a and b, the reading of the quaternion comparison model is (1 + <a, b>) / 2, where <a, b> is the real inner product. "
                    + "Since |a - b|^2 = |a|^2 - 2 <a, b> + |b|^2 and both norms are one, <a, b> = 1 - |a - b|^2 / 2, and the reading is 1 - |a - b|^2 / 4. "
                    + "Here dist(a, b) is the distance |a - b| of a and b as quaternions."),
            Node("normalized-embedding", "exists_normalized_embedding", "A normalized embedding into the unit quaternions",
                StatementSource.FromAuthor(NormalizedEmbeddingFormula()), DescribeRole.Lemma,
                "Let C be a ternary comparison structure on M whose transfer is order sensitive and whose reading is chain connected, takes values arbitrarily close to zero and is the Gram kernel of a map into Euclidean 5-space, and let o be a point of M. "
                    + "Then there is an injective map v from M into the unit quaternions with v(o) = 1 that carries the transfer to v(tri(C, x, y, z)) = v(x) * v(y)^-1 * v(z) and preserves the reading, kappa(C, x, y) = kappa(quaternionModel, v(x), v(y)). "
                    + "The feature-rank embedding gives an injective map w with the same transfer law and with kappa(C, x, y) = (1 + <w(x), w(y)>) / 2. "
                    + "The map v(x) = w(o)^-1 * w(x) is injective and sends o to 1; the transfer law follows from the group identity (w(o)^-1 * p) * (w(o)^-1 * q)^-1 * (w(o)^-1 * r) = w(o)^-1 * (p * q^-1 * r), and the reading is preserved because left multiplication by a unit quaternion preserves the real inner product."),
            Node("range-subgroup", "rangeSubgroup", "The image as a subgroup",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Let C be a ternary comparison structure on M, o a point of M and v a map from M into the unit quaternions with v(o) = 1 and v(tri(C, x, y, z)) = v(x) * v(y)^-1 * v(z) for all x, y and z. "
                    + "The image of v is then a subgroup of the unit quaternions: it contains v(o) = 1, the product v(x) * v(y) is the image v(tri(C, x, o, y)), and the inverse of v(x) is the image v(tri(C, o, x, o)). "
                    + "This definition records the image of v with that subgroup structure."),
            Node("closed-range", "isClosed_range", "Under a complete reading the image is closed",
                StatementSource.FromAuthor(ClosedRangeFormula()), DescribeRole.Lemma,
                "Let C be a ternary comparison structure on M with complete reading and let v be a map from M into the unit quaternions with kappa(C, x, y) = kappa(quaternionModel, v(x), v(y)) for all x and y. "
                    + "Then the image of v is a closed subset of the unit quaternions. "
                    + "Let v(x n) converge to a unit quaternion q. The reading between unit quaternions is 1 - dist^2 / 4, so the readings kappa(C, x m, x n) are within e of one for all large m and n, for every e > 0. "
                    + "Completeness gives a point a whose readings kappa(C, x n, a) tend to one; then dist(v(x n), v(a)) tends to zero, so v(x n) converges to v(a), and q = v(a) lies in the image. "
                    + "Sequentially closed subsets of a metric space are closed."),
            Node("exists-unit-quaternion-equiv", "exists_unitQuaternion_equiv",
                "Complete structures of feature rank five are the unit quaternions",
                StatementSource.FromAuthor(EquivFormula()), DescribeRole.Theorem,
                "Let C be a ternary comparison structure on M whose transfer is order sensitive, whose reading is chain connected, takes values arbitrarily close to zero, is the Gram kernel of a map into Euclidean 5-space, and is complete. "
                    + "Then for every point o of M there is a bijection u from M onto the unit quaternions with u(o) = 1 that carries the transfer of C to the transfer tri(quaternionModel, p, q, r) = p * q^-1 * r of the quaternion comparison model "
                    + "and the reading of C to its reading kappa(quaternionModel, p, q) = (1 + <p, q>) / 2, where <p, q> is the real inner product of quaternions. "
                    + "The feature-rank embedding gives an injective map w from M into the unit quaternions with w(tri(C, x, y, z)) = w(x) * w(y)^-1 * w(z) and kappa(C, x, y) = (1 + <w(x), w(y)>) / 2. "
                    + "The map v(x) = w(o)^-1 * w(x) is injective, sends o to 1, carries the transfer to x * y^-1 * z, and preserves the reading, because left multiplication by a unit quaternion preserves the real inner product. "
                    + "Its image is a subgroup of the unit quaternions: v(x) * v(y) = v(tri(C, x, o, y)) and the inverse of v(x) is v(tri(C, o, x, o)). "
                    + "Between unit quaternions the reading is 1 - |p - q|^2 / 4. "
                    + "Hence if v(x n) converges to a unit quaternion q, the readings kappa(C, x m, x n) tend to one uniformly in m and n, completeness gives a point a whose readings kappa(C, x n, a) tend to one, so v(x n) also converges to v(a), and q = v(a); the image is closed. "
                    + "For every e > 0, a chain of points of M with consecutive readings above 1 - e is carried by v to a chain in the image with the same consecutive readings, and two points that do not commute in the group of C at o, whose product is tri(C, x, o, y), are carried to unit quaternions that do not commute. "
                    + "A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined by such chains is the whole group, so v is a bijection onto the unit quaternions."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-isomorphism-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula LessThan(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula AtMost(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    /// <summary>Closes a body over the carrier M and the structure C on M.</summary>
    private static Formula OverStructure(Formula body) =>
        Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M), body)));

    /// <summary>For every e &gt; 0 there is N such that the body holds.</summary>
    private static Formula Eventually(Formula body) =>
        ForAll("e", Reals, Implies(LessThan(D(0), F.Id("e")), Exists("N", Naturals, body)));

    private static Formula CloseToOne(Formula reading) => LessThan(Sub(D(1), F.Id("e")), reading);

    private static Formula ReadingCompleteFormula()
    {
        Formula x = F.Id("x"), m = F.Id("m"), n = F.Id("n"), a = F.Id("a"), bigN = F.Id("N");
        Formula cauchy = Eventually(ForAllMany(Naturals,
            Implies(AtMost(bigN, m), Implies(AtMost(bigN, n),
                CloseToOne(Call("kappa", C, At(x, m), At(x, n))))), "m", "n"));
        Formula limit = Exists("a", M, Eventually(ForAll("n", Naturals,
            Implies(AtMost(bigN, n), CloseToOne(Call("kappa", C, At(x, n), a))))));
        return OverStructure(Logic(Call("ReadingComplete", C), FormulaLogicOperator.Iff,
            ForAll("x", new Formula.TypeArrow(Naturals, M), Implies(cauchy, limit))));
    }

    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Inv(Formula x) => new Formula.Power(x, Seq(Minus, D(1)));
    private static Formula MapsToUnits => new Formula.TypeArrow(M, Units);

    private static Formula DistanceFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(ForAllMany(Units,
            Equal(Call("kappa", Model, a, b),
                Sub(D(1), Div(new Formula.Power(Call("dist", a, b), D(2)), D(4)))), "a", "b"));
    }

    /// <summary>The reading of C is the quaternion reading along v.</summary>
    private static Formula ReadingPreserved(Formula v)
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return ForAllMany(M, Equal(Call("kappa", C, x, y), Call("kappa", Model, At(v, x), At(v, y))), "x", "y");
    }

    private static Formula NormalizedEmbeddingFormula()
    {
        Formula v = F.Id("v"), o = F.Id("o"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula transfer = ForAllMany(M,
            Equal(At(v, Call("tri", C, x, y, z)), Mul(Mul(At(v, x), Inv(At(v, y))), At(v, z))),
            "x", "y", "z");
        Formula embedding = Exists("v", MapsToUnits,
            And(Call("Injective", v), And(Equal(At(v, o), D(1)), And(transfer, ReadingPreserved(v)))));
        return OverStructure(Implies(Call("Noncommutative", C), Implies(Call("ChainConnected", C),
            Implies(Call("TouchesZero", C), Implies(Call("HasFeatureRank", C, D(5)),
                ForAll("o", M, embedding))))));
    }

    private static Formula ClosedRangeFormula()
    {
        Formula v = F.Id("v");
        return OverStructure(ForAll("v", MapsToUnits,
            Implies(ReadingPreserved(v), Implies(Call("ReadingComplete", C),
                Call("IsClosed", Call("range", v))))));
    }

    private static Formula EquivFormula()
    {
        Formula u = F.Id("u"), o = F.Id("o"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula transfer = ForAllMany(M,
            Equal(At(u, Call("tri", C, x, y, z)), Call("tri", Model, At(u, x), At(u, y), At(u, z))),
            "x", "y", "z");
        Formula reading = ForAllMany(M,
            Equal(Call("kappa", C, x, y), Call("kappa", Model, At(u, x), At(u, y))), "x", "y");
        Formula equivalence = Exists("u", Call("Equiv", M, Units),
            And(Equal(At(u, o), D(1)), And(transfer, reading)));
        return OverStructure(Implies(Call("Noncommutative", C), Implies(Call("ChainConnected", C),
            Implies(Call("TouchesZero", C), Implies(Call("HasFeatureRank", C, D(5)),
                Implies(Call("ReadingComplete", C), ForAll("o", M, equivalence)))))));
    }
}
