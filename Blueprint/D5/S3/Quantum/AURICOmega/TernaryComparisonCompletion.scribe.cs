using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A map from a ternary comparison structure into the unit quaternions that carries its transfer and reading to those of the quaternion comparison model has dense range exactly when the structure is noncommutative and chain connected; a subgroup of the unit quaternions with the induced structure has complete reading exactly when it is closed, and a countable dense subgroup shows that completeness of the reading does not follow from noncommutativity, chain connectedness, readings near zero and feature rank five.",
        H("Dense maps of ternary comparison structures into the unit quaternions"),
        Blocks(
            Node("subgroup-model", "subgroupModel", "The induced structure on a subgroup of the unit quaternions",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Let H be a subgroup of the group unitary(H[R]) of unit quaternions. "
                    + "subgroupModel(H) is the ternary comparison structure whose points are the elements of H, whose transfer is tri(x, y, z) = x * y^-1 * z, and whose reading is kappa(x, y) = (1 + <x, y>) / 2, where <x, y> is the real inner product of quaternions. "
                    + "The transfer of three elements of H lies in H because H is closed under products and inverses, and both operations are those of the quaternion comparison model quaternionModel restricted to H. "
                    + "Each identity required of a ternary comparison structure holds in subgroupModel(H) because it holds in quaternionModel; in particular the reading of two elements of H equals one exactly when they are equal, since elements of H are equal exactly when they are equal as unit quaternions."),
            Node("dense-range-iff", "denseRange_iff",
                "Density criterion for transfer- and reading-preserving maps",
                StatementSource.FromAuthor(DenseRangeIffFormula()), DescribeRole.Theorem,
                Text("Let C be a ternary comparison structure on M and v a map from M into the unit quaternions with v(tri(C, x, y, z)) = v(x) * v(y)^-1 * v(z), the transfer of the quaternion comparison model, and kappa(C, x, y) = kappa(quaternionModel, v(x), v(y)) = (1 + <v(x), v(y)>) / 2 for all points, where <p, q> is the real inner product of quaternions. "
                    + "Then v has dense range if and only if C is noncommutative and chain connected. "
                    + "No feature rank, no readings near zero and no completeness of the reading are assumed: feature rank five follows from the existence of v alone, since composing v with the feature map of the unit quaternions realizes the reading of C in Euclidean five-space, and readings near zero follow once the range of v is dense; neither is a hypothesis of the criterion, and these consequences are not among the formal statements of the module. "
                    + "Such a map is injective, because a reading equal to one means equality both in C and in the unit quaternions. "
                    + "Dense range gives the two properties. The triples (a, b, c) of unit quaternions with a * b^-1 * c different from c * b^-1 * a form an open set, nonempty because i * 1^-1 * j = k and j * 1^-1 * i = -k; the triples of points of the range of v are dense among all triples, so some triple v(x), v(y), v(z) lies in it, and then tri(C, x, y, z) differs from tri(C, z, y, x) because their images under v differ. "
                    + "The unit quaternions form the unit three-sphere in a real space of dimension four, which is connected. For d > 0 let P(a, b) say that any two points of M whose images lie within distance d / 3 of a and of b are joined by a chain of points of M whose consecutive images are at distance less than d; P(a, b) holds whenever |a - b| < d / 3 by the triangle inequality, and P is transitive because the range of v has a point within distance d / 3 of every unit quaternion. "
                    + "On a connected space a transitive relation that holds between each point and all points of a neighbourhood holds between all pairs, so any two points of M are joined by such chains. "
                    + "Between unit quaternions the reading is 1 - |p - q|^2 / 4, so with d = min(1, e) consecutive readings along the chain exceed 1 - e, which is chain connectedness. "
                    + "Conversely, let C be noncommutative and chain connected, and fix a point o of M. The normalized map w(x) = v(o)^-1 * v(x) sends o to 1, carries the transfer of C to x * y^-1 * z and preserves the reading, because left multiplication by a unit quaternion preserves the inner product. "
                    + "Its image contains 1 and is closed under products and inverses, since w(x) * w(y) = w(tri(C, x, o, y)) and w(x)^-1 = w(tri(C, o, x, o)), so its closure K is a closed subgroup of the unit quaternions. "
                    + "Two unit quaternions at distance less than min(1, e) have reading above 1 - e, and every point of K has points of the image of w that near; hence the chains of C, carried by w, give chains in K with consecutive readings above 1 - e between any two points of K. "
                    + "Two points of M that do not commute in the group of C at o, whose product is tri(C, x, o, y), are carried to unit quaternions that do not commute, and both lie in K. "
                    + "A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined by such chains for every e > 0 is the whole group, by eq_top_of_isClosed_of_chainConnected in "),
                    Ref("D5/B/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup"),
                    Text("; so K is the whole group, the image of w is dense, and so is its left translate by v(o), the image of v. "
                    + "When M is empty both sides of the equivalence are false. "
                    + "For the inclusion of a subgroup H of the unit quaternions, with the induced structure subgroupModel(H), the criterion reads: H is dense if and only if subgroupModel(H) is noncommutative and chain connected. "
                    + "Neither property on the right can be omitted: the eight quaternions 1, -1, i, -i, j, -j, k, -k form a finite subgroup whose induced structure is noncommutative but not dense, and indeed not chain connected, since distinct points of a finite set are at least some fixed distance apart; the unit quaternions cos t + sin t * i form a closed connected subgroup whose induced structure is chain connected and commutative, and it is not dense. These examples are not among the formal statements of the module.")),
            Node("complete-iff-closed", "subgroupModel_readingComplete_iff",
                "On a subgroup, completeness of the reading is closedness",
                StatementSource.FromAuthor(CompleteIffClosedFormula()), DescribeRole.Theorem,
                "For a subgroup H of the unit quaternions, the reading of subgroupModel(H) is complete exactly when H is a closed subset of the unit quaternions. "
                    + "If the reading is complete, the inclusion of H into the unit quaternions preserves the reading, and the image of a reading-preserving map from a structure with complete reading into the unit quaternions is closed; this image is H. "
                    + "Conversely, let H be closed. The unit quaternions form a closed subset of the complete space of quaternions, so they are complete, and H, closed in them, is complete. "
                    + "Since the reading is 1 - |p - q|^2 / 4, a sequence x in H whose readings kappa(x(m), x(n)) exceed 1 - e^2 / 4 for all m and n beyond some N satisfies |x(m) - x(n)| < e there; so a sequence whose readings tend to one uniformly is a Cauchy sequence and converges to some a in H. "
                    + "For all n beyond some N the distance |x(n) - a| is less than min(1, e), and then the reading kappa(x(n), a) exceeds 1 - e, which is completeness of the reading. "
                    + "The statement is the classical fact that a subset of a complete metric space is complete exactly when it is closed, read through the reading."),
            Node("independence", "exists_subgroupModel_not_readingComplete",
                "Completeness does not follow from the other hypotheses",
                StatementSource.FromAuthor(IndependenceFormula()), DescribeRole.Theorem,
                Text("There is a subgroup H of the unit quaternions such that subgroupModel(H) is noncommutative, chain connected, its reading touches zero and it has feature rank five, while its reading is not complete. "
                    + "HasFeatureRank(subgroupModel(H), 5) asserts that there is a map from H into Euclidean five-space whose inner products are the readings, that is, a realization of the reading in five dimensions. "
                    + "Hence completeness of the reading is not implied by the other four hypotheses under which a complete structure is identified with the unit quaternions. "
                    + "The unit quaternions form a separable metric space, so they have a countable dense subset S, and the subgroup H generated by S, the image of the free group on S, is countable and dense. "
                    + "The unit quaternions are uncountable: for every t in [-1, 1] the quaternion with real part t, i-coordinate sqrt(1 - t^2) and the other coordinates 0 has norm one, so the real parts of unit quaternions fill the uncountable interval [-1, 1]. "
                    + "The density criterion, applied to the inclusion of H, shows that subgroupModel(H) is noncommutative and chain connected. "
                    + "The reading is continuous, so for e > 0 the pairs (p, q) of unit quaternions with reading below e form an open set, nonempty because the reading of 1 and -1 is 0; it contains a pair of elements of H, so the reading touches zero. "
                    + "The feature map of the unit quaternions, which sends q to (1 / sqrt 2) * (1, re q, imI q, imJ q, imK q), restricted to H realizes the reading in five dimensions. "
                    + "A noncommutative, chain-connected ternary comparison structure whose reading is realized in Euclidean r-space has 5 <= r, by five_le_of_hasFeatureRank in "),
                    Ref("D5/B/S3/Quantum/AURICOmega/TernaryComparisonRankFive"),
                    Text("; so five is the least such dimension for subgroupModel(H), and this combination is not among the formal statements of the module. "
                    + "If the reading of subgroupModel(H) were complete, H would be closed by the characterization of completeness on subgroups, so H would equal its closure, which is the whole group of unit quaternions since H is dense, contradicting the countability of H.")))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Node(id, selector, title, statement, role, Text(prose));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role,
        params Inline[] prose) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-completion-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(prose)), role);

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

    private static Formula DenseRangeIffFormula()
    {
        Formula v = F.Id("v"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula transfer = ForAllMany(M,
            Equal(At(v, Call("tri", C, x, y, z)), Call("tri", Model, At(v, x), At(v, y), At(v, z))),
            "x", "y", "z");
        Formula reading = ForAllMany(M,
            Equal(Call("kappa", C, x, y), Call("kappa", Model, At(v, x), At(v, y))), "x", "y");
        Formula criterion = Logic(Call("DenseRange", v), FormulaLogicOperator.Iff,
            And(Call("Noncommutative", C), Call("ChainConnected", C)));
        return Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M),
            ForAll("v", new Formula.TypeArrow(M, Units),
                Implies(transfer, Implies(reading, criterion))))));
    }

    private static Formula CompleteIffClosedFormula() =>
        Disp(ForAll("H", Subgroups, Logic(Call("ReadingComplete", Induced), FormulaLogicOperator.Iff,
            Call("IsClosed", F.Id("H")))));

    private static Formula IndependenceFormula() =>
        Disp(Exists("H", Subgroups,
            FourProperties(Induced, rank => And(rank, new Formula.Not(Call("ReadingComplete", Induced))))));
}
