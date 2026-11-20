using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Without completeness of the reading, a noncommutative, chain-connected ternary comparison structure of feature rank five whose reading touches zero embeds into the unit quaternions with dense range; a subgroup of the unit quaternions with the induced structure has complete reading exactly when it is closed, a dense subgroup satisfies the other four hypotheses, and a countable dense subgroup shows that completeness does not follow from them.",
        H("Rank-five ternary comparison structures without completeness"),
        Blocks(
            Node("subgroup-model", "subgroupModel", "The induced structure on a subgroup of the unit quaternions",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Let H be a subgroup of the group unitary(H[R]) of unit quaternions. "
                    + "subgroupModel(H) is the ternary comparison structure whose points are the elements of H, whose transfer is tri(x, y, z) = x * y^-1 * z, and whose reading is kappa(x, y) = (1 + <x, y>) / 2, where <x, y> is the real inner product of quaternions. "
                    + "The transfer of three elements of H lies in H because H is closed under products and inverses, and both operations are those of the quaternion comparison model quaternionModel restricted to H. "
                    + "Each identity required of a ternary comparison structure holds in subgroupModel(H) because it holds in quaternionModel; in particular the reading of two elements of H equals one exactly when they are equal, since elements of H are equal exactly when they are equal as unit quaternions."),
            Node("dense-range", "exists_unitQuaternion_embedding_denseRange",
                "Without completeness, the embedding into the unit quaternions has dense range",
                StatementSource.FromAuthor(DenseRangeFormula()), DescribeRole.Theorem,
                "Let C be a ternary comparison structure on M whose transfer is order sensitive, whose reading is chain connected and takes values arbitrarily close to zero, and which has feature rank five: HasFeatureRank(C, 5) asserts that there is a map from M into Euclidean five-space whose inner products are the readings of C, that is, a realization of the reading in five dimensions. "
                    + "Completeness of the reading is not assumed. "
                    + "Then for every point o of M there is an injective map u from M into the unit quaternions with u(o) = 1 and dense range, which carries the transfer of C to the transfer p * q^-1 * r of the quaternion comparison model and preserves the reading, kappa(C, x, y) = (1 + <u(x), u(y)>) / 2. "
                    + "Proof. The normalized embedding of such a structure gives an injective map u with u(o) = 1, u(tri(C, x, y, z)) = u(x) * u(y)^-1 * u(z) and preserved reading. "
                    + "Its image contains 1 and is closed under products and inverses, since u(x) * u(y) = u(tri(C, x, o, y)) and u(x)^-1 = u(tri(C, o, x, o)); multiplication and inversion are continuous, so the closure K of the image is a closed subgroup of the unit quaternions. "
                    + "Between unit quaternions the reading is 1 - |p - q|^2 / 4, so two unit quaternions at distance less than min(1, e) have reading above 1 - e. "
                    + "For every e > 0, two points of the image are joined by a chain in the image whose consecutive readings exceed 1 - e, namely the image of such a chain in M. "
                    + "Two points of K have points of the image within distance min(1, e), so every two points of K are joined by a chain in K whose consecutive readings exceed 1 - e. "
                    + "Two points of M that do not commute in the group of C at o, whose product is tri(C, x, o, y), are carried to unit quaternions that do not commute, and both lie in K. "
                    + "A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined by such chains for every e > 0 is the whole group, so K is the whole group and the image of u is dense. "
                    + "When the reading of C is moreover complete, the image is closed, hence the whole group, and u is a bijection. "
                    + "Without completeness u need not be onto: the countable dense subgroup constructed below has an induced structure satisfying all four hypotheses, and no map from a countable set onto the uncountable set of unit quaternions exists; this consequence is not among the formal statements of the module."),
            Node("complete-iff-closed", "subgroupModel_readingComplete_iff",
                "On a subgroup, completeness of the reading is closedness",
                StatementSource.FromAuthor(CompleteIffClosedFormula()), DescribeRole.Theorem,
                "For a subgroup H of the unit quaternions, the reading of subgroupModel(H) is complete exactly when H is a closed subset of the unit quaternions. "
                    + "If the reading is complete, the inclusion of H into the unit quaternions preserves the reading, and the image of a reading-preserving map from a structure with complete reading into the unit quaternions is closed; this image is H. "
                    + "Conversely, let H be closed. The unit quaternions form a closed subset of the complete space of quaternions, so they are complete, and H, closed in them, is complete. "
                    + "Since the reading is 1 - |p - q|^2 / 4, a sequence x in H whose readings kappa(x(m), x(n)) exceed 1 - e^2 / 4 for all m and n beyond some N satisfies |x(m) - x(n)| < e there; so a sequence whose readings tend to one uniformly is a Cauchy sequence and converges to some a in H. "
                    + "For all n beyond some N the distance |x(n) - a| is less than min(1, e), and then the reading kappa(x(n), a) exceeds 1 - e, which is completeness of the reading. "
                    + "The statement is the classical fact that a subset of a complete metric space is complete exactly when it is closed, read through the reading."),
            Node("dense-hypotheses", "subgroupModel_of_dense",
                "A dense subgroup satisfies every hypothesis except completeness",
                StatementSource.FromAuthor(DenseHypothesesFormula()), DescribeRole.Theorem,
                "Let H be a dense subgroup of the unit quaternions. Then subgroupModel(H) is noncommutative, chain connected, its reading touches zero, and it has feature rank five. "
                    + "Order sensitivity: the pairs (p, q) of unit quaternions with p * q different from q * p form an open set, which is nonempty because i * j = k and j * i = -k. "
                    + "The pairs of elements of H are dense among all pairs, so H contains such a pair p, q, and tri(p, 1, q) = p * q differs from tri(q, 1, p) = q * p. "
                    + "Readings near zero: the reading is continuous, so for e > 0 the pairs (p, q) with kappa(p, q) < e form an open set, nonempty because the reading of 1 and -1 is 0; it contains a pair of elements of H. "
                    + "Chains: the unit quaternions are the unit three-sphere in a real space of dimension four, which is connected. "
                    + "Fix d > 0 and let P(a, b) say that any element of H within distance d / 3 of a and any element of H within distance d / 3 of b are joined by a chain of elements of H whose consecutive distances are less than d. "
                    + "By the triangle inequality P(a, b) holds whenever |a - b| < d / 3, and P is transitive, because H has an element within distance d / 3 of the middle point at which two chains can be joined. "
                    + "On a connected space a transitive relation that holds between each point and all points of a neighbourhood holds between all pairs of points, so any two elements of H are joined by chains with steps of distance less than d. "
                    + "Taking d = min(1, e), consecutive readings along such a chain exceed 1 - e. "
                    + "Feature rank five: the feature map of the unit quaternions, which sends q to (1 / sqrt 2) * (1, re q, imI q, imJ q, imK q) in Euclidean five-space, restricted to H realizes the reading of subgroupModel(H) in five dimensions. "
                    + "A noncommutative, chain-connected ternary comparison structure has no such realization in fewer than five dimensions, by the lower bound for the feature rank of these structures; so five is the least such dimension for subgroupModel(H), and this combination is not among the formal statements of the module. "
                    + "Density cannot be omitted: the trivial subgroup is closed and its structure has a single point, so its transfer is not order sensitive; this consequence is not among the formal statements of the module."),
            Node("independence", "exists_subgroupModel_not_readingComplete",
                "Completeness does not follow from the other hypotheses",
                StatementSource.FromAuthor(IndependenceFormula()), DescribeRole.Theorem,
                "There is a subgroup H of the unit quaternions such that subgroupModel(H) is noncommutative, chain connected, its reading touches zero and it has feature rank five, while its reading is not complete. "
                    + "Hence completeness of the reading is not implied by the other four hypotheses under which a complete structure is identified with the unit quaternions. "
                    + "The unit quaternions form a separable metric space, so they have a countable dense subset S, and the subgroup H generated by S, the image of the free group on S, is countable and dense. "
                    + "The unit quaternions are uncountable: for every t in [-1, 1] the quaternion with real part t, i-coordinate sqrt(1 - t^2) and the other coordinates 0 has norm one, so the real parts of unit quaternions fill the uncountable interval [-1, 1]. "
                    + "By the previous theorem subgroupModel(H) has the four properties. "
                    + "If its reading were complete, H would be closed by the characterization of completeness on subgroups, so H would equal its closure, which is the whole group of unit quaternions since H is dense, contradicting the countability of H."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-completion-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
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
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Subgroups => Call("Subgroup", Units);

    /// <summary>The induced structure subgroupModel(H) on the subgroup H.</summary>
    private static Formula Induced => Call("subgroupModel", F.Id("H"));

    /// <summary>The four hypotheses other than completeness, for the structure S, as right-nested
    /// conjunctions whose innermost conjunct is the given tail.</summary>
    private static Formula FourProperties(Formula s, Func<Formula, Formula> tail) =>
        And(Call("Noncommutative", s), And(Call("ChainConnected", s),
            And(Call("TouchesZero", s), tail(Call("HasFeatureRank", s, D(5))))));

    private static Formula DenseRangeFormula()
    {
        Formula u = F.Id("u"), o = F.Id("o"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula transfer = ForAllMany(M,
            Equal(At(u, Call("tri", C, x, y, z)), Call("tri", Model, At(u, x), At(u, y), At(u, z))),
            "x", "y", "z");
        Formula reading = ForAllMany(M,
            Equal(Call("kappa", C, x, y), Call("kappa", Model, At(u, x), At(u, y))), "x", "y");
        Formula embedding = Exists("u", new Formula.TypeArrow(M, Units),
            And(Call("Injective", u), And(Equal(At(u, o), D(1)),
                And(Call("DenseRange", u), And(transfer, reading)))));
        return Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M),
            Implies(Call("Noncommutative", C), Implies(Call("ChainConnected", C),
                Implies(Call("TouchesZero", C), Implies(Call("HasFeatureRank", C, D(5)),
                    ForAll("o", M, embedding))))))));
    }

    private static Formula CompleteIffClosedFormula() =>
        Disp(ForAll("H", Subgroups, Logic(Call("ReadingComplete", Induced), FormulaLogicOperator.Iff,
            Call("IsClosed", F.Id("H")))));

    private static Formula DenseHypothesesFormula() =>
        Disp(ForAll("H", Subgroups, Implies(Call("Dense", F.Id("H")), FourProperties(Induced, rank => rank))));

    private static Formula IndependenceFormula() =>
        Disp(Exists("H", Subgroups,
            FourProperties(Induced, rank => And(rank, new Formula.Not(Call("ReadingComplete", Induced))))));
}
