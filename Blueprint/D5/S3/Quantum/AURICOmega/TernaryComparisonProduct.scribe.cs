using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.";
    private static LibraryNoteRef Schur => LibraryNoteRef.Create("D5/L/QuantumBounds/schur1911boundedforms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Products of ternary comparison structures, with multiplied feature ranks.",
        H("Products of ternary comparison structures"),
        Blocks(
            Node("prod", "prod", "The product structure",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Schur),
                "For ternary comparison structures C on M and D on N, prod C D is the ternary comparison structure on M x N defined componentwise. "
                    + "Its transfer sends p, q, r to the pair whose first component is the transfer of C applied to the first components, tri of C at p.1, q.1, r.1, "
                    + "and whose second component is the transfer of D applied to the second components, tri of D at p.2, q.2, r.2. "
                    + "Its reading at p, q is the reading of C at p.1, q.1 times the reading of D at p.2, q.2. "
                    + "The transfer identities and the invariance of the reading hold in each coordinate. "
                    + "The product reading equals one exactly on the diagonal because the readings of C and of D both lie in the interval from 0 to 1, so a product equal to one forces both factors to be one. "
                    + "The upper bound one for the reading of C at x, y holds because the Gram form of C for the pair x, y with coefficients 1 and -1 equals 2 minus twice that reading and is nonnegative; the same holds for D. "
                    + "Every finite Gram matrix of the product reading is the entrywise product of the corresponding Gram matrices of the readings of C and of D, "
                    + "and the entrywise product of two positive semidefinite matrices is positive semidefinite by the Schur product theorem.",
                DescribeRole.Definition),
            Node("has-feature-rank", "prod_hasFeatureRank", "Feature ranks multiply",
                StatementSource.FromAuthor(FeatureRankFormula()), AssessedProvenance.FromRepo(),
                "If the reading of C at x, y is the inner product of f x and f y for a map f from M into Euclidean r-space, and the reading of D at u, v is the inner product of g u and g v for a map g from N into Euclidean s-space, "
                    + "then the map sending p to the vector with coordinates (f p.1)_i * (g p.2)_j, indexed by the pairs (i, j) enumerated as Fin (r * s), lands in Euclidean (r * s)-space. "
                    + "Its inner products are the double sums over i and j of (f p.1)_i (f q.1)_i (g p.2)_j (g q.2)_j, which factor as the product of the two inner products, that is the product reading.",
                DescribeRole.Theorem),
            Node("chain-connected", "prod_chainConnected", "Chain connectivity of the product",
                StatementSource.FromAuthor(ChainConnectedFormula()), AssessedProvenance.FromRepo(),
                "Given e > 0 and points (u1, u2) and (v1, v2), a chain from u1 to v1 in M with consecutive readings above 1 - e becomes a chain from (u1, u2) to (v1, u2) in the product, "
                    + "because the second coordinate stays at u2 and the reading of u2 with itself is one. "
                    + "Likewise a chain from u2 to v2 in N becomes a chain from (v1, u2) to (v1, v2). Concatenating the two chains joins the given points.",
                DescribeRole.Proposition),
            Node("noncommutative-left", "prod_noncommutative_left", "Order sensitivity from the left factor",
                StatementSource.FromAuthor(NoncommutativeFormula()), AssessedProvenance.FromRepo(),
                "If tri x y z differs from tri z y x in M and w is any point of the nonempty carrier N, "
                    + "then the triple (x, w), (y, w), (z, w) is order sensitive in the product, since the first coordinates of the two transfers already differ.",
                DescribeRole.Proposition),
            Node("touches-zero-left", "prod_touchesZero_left", "Small readings from the left factor",
                StatementSource.FromAuthor(TouchesZeroFormula()), AssessedProvenance.FromRepo(),
                "Given e > 0, choose x and y in M with reading below e and any point w of the nonempty carrier N. "
                    + "The product reading of (x, w) and (y, w) is the reading of x and y times the reading of w with itself, which is one, so it is below e.",
                DescribeRole.Proposition))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-product-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula M => F.Id("M");
    private static Formula N => F.Id("N");
    private static Formula C => F.Id("C");
    private static Formula Dv => F.Id("D");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Product => Call("prod", C, Dv);

    /// <summary>Closes a body over the carriers M and N and the structures C on M and D on N.</summary>
    private static Formula OverFactors(Formula body) =>
        Disp(ForAllMany(TypeStar,
            ForAll("C", Call("TernaryComparison", M), ForAll("D", Call("TernaryComparison", N), body)),
            "M", "N"));

    /// <summary>Adds the instance argument that the carrier N is nonempty.</summary>
    private static Formula NonemptyRight(Formula body) =>
        Seq(OpenBracket, Call("Nonempty", N), CloseBracket, Sp, body);

    private static Formula FeatureRankFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s");
        return OverFactors(ForAllMany(Naturals,
            Implies(Call("HasFeatureRank", C, r), Implies(Call("HasFeatureRank", Dv, s),
                Call("HasFeatureRank", Product, new Formula.Binary(r, FormulaBinaryOperator.Multiply, s)))),
            "r", "s"));
    }

    private static Formula ChainConnectedFormula() =>
        OverFactors(Implies(Call("ChainConnected", C),
            Implies(Call("ChainConnected", Dv), Call("ChainConnected", Product))));

    private static Formula NoncommutativeFormula() =>
        OverFactors(NonemptyRight(Implies(Call("Noncommutative", C), Call("Noncommutative", Product))));

    private static Formula TouchesZeroFormula() =>
        OverFactors(NonemptyRight(Implies(Call("TouchesZero", C), Call("TouchesZero", Product))));
}
