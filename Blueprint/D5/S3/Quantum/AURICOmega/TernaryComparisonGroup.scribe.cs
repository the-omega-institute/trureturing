using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonGroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonGroup.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Semigroups/certaine1943ternary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Origin-free ternary comparison structures become groups at every base point.",
        H("Ternary comparison structures and their groups"),
        Blocks(
            Node("ternary-comparison", "TernaryComparison", "Ternary comparison structures",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                "A ternary comparison structure on a type M consists of a transfer tri : M -> M -> M -> M and a real reading kappa : M -> M -> R. "
                    + "The transfer satisfies tri x x z = z, tri x z z = x and tri (tri x y z) u v = tri x y (tri z u v) for all x, y, z, u, v. "
                    + "The reading satisfies kappa x y = kappa y x, kappa x y = 1 exactly when x = y, 0 <= kappa x y, "
                    + "kappa (tri x u v) (tri y u v) = kappa x y and kappa (tri u v x) (tri u v y) = kappa x y. "
                    + "For every natural number n, every family x : Fin n -> M and every c : Fin n -> R, the Gram form sum over i and j of c i * c j * kappa (x i) (x j) is nonnegative. "
                    + "No base point, binary product or topology is part of the data. The three transfer identities are the heap identities; the reading is additional structure.",
                DescribeRole.Definition),
            Node("noncommutative", "Noncommutative", "Order sensitivity of the transfer",
                StatementSource.FromAuthor(NoncommutativeFormula()), AssessedProvenance.FromRepo(),
                "The transfer is order sensitive when exchanging its two outer arguments changes its value for some triple.",
                DescribeRole.Definition),
            Node("touches-zero", "TouchesZero", "Readings arbitrarily close to zero",
                StatementSource.FromAuthor(TouchesZeroFormula()), AssessedProvenance.FromRepo(),
                "For every positive real e some pair of points has reading below e.",
                DescribeRole.Definition),
            Node("chain-connected", "ChainConnected", "Chain connectivity of the reading",
                StatementSource.FromAuthor(ChainConnectedFormula()), AssessedProvenance.FromRepo(),
                "For every positive real e, any two points are related by the reflexive transitive closure of the relation a, b with 1 - e < kappa a b; "
                    + "that is, they are joined by a finite chain whose consecutive readings exceed 1 - e.",
                DescribeRole.Definition),
            Node("gram-rank-le", "GramRankLE", "Gram rank bounded by r",
                StatementSource.FromAuthor(GramRankFormula()), AssessedProvenance.FromRepo(),
                "Every finite Gram matrix of the reading, indexed by Fin n with entries kappa (x i) (x j), has rank at most r.",
                DescribeRole.Definition),
            Node("has-feature-rank", "HasFeatureRank", "Feature maps into Euclidean r-space",
                StatementSource.FromAuthor(FeatureRankFormula()), AssessedProvenance.FromRepo(),
                "The reading is the real inner product of the images of a single map f from M into the Euclidean space of dimension r.",
                DescribeRole.Definition),
            Node("group-at", "groupAt", "The group at a base point",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                "For a base point o, groupAt C o is the group structure on M with product x * y = tri x o y, identity o and inverse x^-1 = tri o x o. "
                    + "Associativity is the transfer associativity with the two middle arguments equal to o. "
                    + "The left and right identity laws are tri o o y = y and tri x o o = x. "
                    + "The inverse law tri (tri o x o) o x = o follows from associativity and the two cancellation identities.",
                DescribeRole.Definition),
            Node("tri-eq-mul-inv-mul", "tri_eq_mul_inv_mul", "The transfer recovered at any base point",
                StatementSource.FromAuthor(RecoveryFormula()), AssessedProvenance.FromRepo(Source),
                "In the group at o, x * y^-1 * z unfolds to tri (tri x o (tri o y o)) o z. "
                    + "Two applications of associativity and tri o o w = w reduce it to tri x o (tri o y z), and one reverse associativity step followed by tri x o o = x gives tri x y z. "
                    + "The base point o is arbitrary: the transfer is the same expression x * y^-1 * z in every one of these groups.",
                DescribeRole.Theorem),
            Node("base-change-bijective", "baseChange_bijective", "Base change is a bijection",
                StatementSource.FromAuthor(BaseChangeBijectiveFormula()), AssessedProvenance.FromRepo(Source),
                "For base points o and p, the map x -> tri x o p has the two-sided inverse x -> tri x p o: by associativity and the cancellation identities, tri (tri x o p) p o = x and tri (tri x p o) o p = x.",
                DescribeRole.Theorem),
            Node("noncommutative-iff", "noncommutative_iff", "Order sensitivity and noncommutativity",
                StatementSource.FromAuthor(NoncommutativeIffFormula()), AssessedProvenance.FromRepo(Source),
                "If the group at o were commutative, the recovery formula would give tri x y z = x * y^-1 * z = z * y^-1 * x = tri z y x for every triple, so an order-sensitive triple forces two noncommuting elements. "
                    + "Conversely, two elements x and y with tri x o y different from tri y o x form the order-sensitive triple (x, o, y).",
                DescribeRole.Theorem),
            Node("kappa-self", "kappa_self", "The reading on the diagonal",
                StatementSource.FromAuthor(KappaSelfFormula()), AssessedProvenance.FromRepo(),
                "This is the reverse direction of the axiom that the reading equals one exactly on the diagonal.",
                DescribeRole.Lemma))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-group-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    /// <summary>Closes a body over the carrier M and the structure C on M.</summary>
    private static Formula OverStructure(Formula body) =>
        Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M), body)));

    private static Formula Tri(Formula x, Formula y, Formula z) => Call("tri", C, x, y, z);
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", C, x, y);
    private static Formula Group(Formula o) => Call("groupAt", C, o);
    private static Formula Mul(Formula g, Formula x, Formula y) => Call("mul", g, x, y);
    private static Formula Inv(Formula g, Formula x) => Call("inv", g, x);

    private static Formula NoncommutativeFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        return OverStructure(Logic(Call("Noncommutative", C), FormulaLogicOperator.Iff,
            ExistsMany(M, Rel(Tri(x, y, z), FormulaRelationOperator.NotEqual, Tri(z, y, x)), "x", "y", "z")));
    }

    private static Formula TouchesZeroFormula()
    {
        Formula e = F.Id("e"), x = F.Id("x"), y = F.Id("y");
        return OverStructure(Logic(Call("TouchesZero", C), FormulaLogicOperator.Iff,
            ForAll("e", Reals, Logic(Rel(D(0), FormulaRelationOperator.LessThan, e),
                FormulaLogicOperator.Implies,
                ExistsMany(M, Rel(Kappa(x, y), FormulaRelationOperator.LessThan, e), "x", "y")))));
    }

    private static Formula ChainConnectedFormula()
    {
        Formula e = F.Id("e"), x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula step = Seq(LambdaLower, Sp, a, Sp, b, Dot, Sp,
            Rel(new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, e), FormulaRelationOperator.LessThan, Kappa(a, b)));
        return OverStructure(Logic(Call("ChainConnected", C), FormulaLogicOperator.Iff,
            ForAll("e", Reals, Logic(Rel(D(0), FormulaRelationOperator.LessThan, e),
                FormulaLogicOperator.Implies,
                ForAllMany(M, Call("ReflTransGen", step, x, y), "x", "y")))));
    }

    private static Formula GramRankFormula()
    {
        Formula r = F.Id("r"), n = F.Id("n"), x = F.Id("x"), i = F.Id("i"), j = F.Id("j");
        Formula entry = Kappa(new Formula.Apply(x, [i]), new Formula.Apply(x, [j]));
        Formula matrix = new Formula.Subscript(Seq(Open, entry, Close), Seq(i, Comma, j, Sp, InMacro, Sp, Call("Fin", n)));
        return OverStructure(ForAll("r", Naturals, Logic(Call("GramRankLE", C, r), FormulaLogicOperator.Iff,
            ForAll("n", Naturals, ForAll("x", new Formula.TypeArrow(Call("Fin", n), M),
                Rel(Call("rank", matrix), FormulaRelationOperator.LessThanOrEqual, r))))));
    }

    private static Formula FeatureRankFormula()
    {
        Formula r = F.Id("r"), phi = F.Id("f"), x = F.Id("x"), y = F.Id("y");
        Formula space = Call("EuclideanSpace", Reals, Call("Fin", r));
        Formula inner = new Formula.Subscript(
            Seq(Langle, Sp, new Formula.Apply(phi, [x]), Comma, Sp, new Formula.Apply(phi, [y]), Sp, Rangle), Reals);
        return OverStructure(ForAll("r", Naturals, Logic(Call("HasFeatureRank", C, r), FormulaLogicOperator.Iff,
            Exists("f", new Formula.TypeArrow(M, space),
                ForAllMany(M, Equal(Kappa(x, y), inner), "x", "y")))));
    }

    private static Formula RecoveryFormula()
    {
        Formula o = F.Id("o"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula g = Group(o);
        return OverStructure(ForAllMany(M,
            Equal(Tri(x, y, z), Mul(g, Mul(g, x, Inv(g, y)), z)), "o", "x", "y", "z"));
    }

    private static Formula BaseChangeBijectiveFormula()
    {
        Formula o = F.Id("o"), p = F.Id("p"), x = F.Id("x");
        Formula map = Seq(x, Sp, Mapsto, Sp, Tri(x, o, p));
        return OverStructure(ForAllMany(M, Call("Bijective", map), "o", "p"));
    }

    private static Formula NoncommutativeIffFormula()
    {
        Formula o = F.Id("o"), x = F.Id("x"), y = F.Id("y");
        return OverStructure(ForAll("o", M, Logic(Call("Noncommutative", C), FormulaLogicOperator.Iff,
            ExistsMany(M, Rel(Tri(x, o, y), FormulaRelationOperator.NotEqual, Tri(y, o, x)), "x", "y"))));
    }

    private static Formula KappaSelfFormula()
    {
        Formula x = F.Id("x");
        return OverStructure(ForAll("x", M, Equal(Kappa(x, x), D(1))));
    }
}
