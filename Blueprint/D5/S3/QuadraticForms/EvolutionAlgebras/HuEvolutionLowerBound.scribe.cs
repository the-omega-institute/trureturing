using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class HuEvolutionFormula
{
    internal static Formula Name(string s) => Seq(Operatorname, Grp(F.Id(s)));
    internal static Formula Call(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    internal static Formula Named(string s, params Formula[] a) => Call(Name(s), a);
    internal static Formula V(string s) => F.Id(s);
    internal static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    internal static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    internal static Formula Par(Formula f) => Seq(Open, f, Close);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    internal static Formula Coord(Formula d) => Named("Coord", d);
    internal static Formula Product(Formula d) => Named("Product", d);
    internal static Formula Sub(Formula d) => Named("Submodule", C, Coord(d));
    internal static Formula Top => Name("top");
    internal static Formula Bot => Name("bot");
    internal static Formula Square(Formula mu, Formula u) => Named("square", mu, u);
    internal static Formula NatBasis(Formula mu) => Named("hasNaturalBasis", mu);
    internal static Formula Emb(Formula mu, Formula n) => Named("hasEvolutionEmbedding", mu, n);
    internal static Formula Perfect(Formula mu) => Named("perfect", mu);
    internal static Formula Comm(Formula mu) => Named("commutative", mu);
    internal static Formula Fin(Formula d) => Named("Fin", d);
    internal static Formula Linear(Formula d, Formula n) => Named("LinearMap", C, Coord(d), Coord(n));
    internal static Formula Hom(Formula d, Formula mu, Formula nu, Formula f) =>
        All("x", Coord(d), All("y", Coord(d), Eq(Call(f, Call(mu, V("x"), V("y"))),
            Call(nu, Call(f, V("x")), Call(f, V("y"))))));
    internal static Formula EmbData(Formula d, Formula nu, Formula f, Formula mu) =>
        And(NatBasis(nu), And(Named("Injective", f), Hom(d, mu, nu, f)));
    internal static DocumentBlock.Describe Def(string prefix, string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(prefix + name), H(title),
            StatementSource.FromAuthor(f is Formula.Layout ? f : Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}

internal sealed class HuEvolutionLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.";
    public DocumentDefinition Create()
    {
        var d = F.Id("d"); var n = F.Id("n"); var mu = F.Id("mu"); var w = F.Id("W");
        var c = HuEvolutionFormula.C; var nat = HuEvolutionFormula.N;
        return DocumentDefinition.Create(ScribeNode.Create(
            "A perfect complex bilinear algebra with a square-zero subspace of rank s requires at least d+s evolution coordinates.",
            H("Square-zero subspaces and evolution embedding dimension"),
            Blocks(
                HuEvolutionFormula.Def(Prefix, "Coord", "Complex coordinate spaces",
                    HuEvolutionFormula.All("d", nat, HuEvolutionFormula.Eq(HuEvolutionFormula.Coord(d),
                        Seq(HuEvolutionFormula.Fin(d), Sp, To, Sp, c))), "The dimension d is arbitrary, including zero."),
                HuEvolutionFormula.Def(Prefix, "Product", "Bilinear multiplication",
                    HuEvolutionFormula.All("d", nat, HuEvolutionFormula.Eq(HuEvolutionFormula.Product(d),
                        HuEvolutionFormula.Named("LinearMap", c, HuEvolutionFormula.Coord(d),
                            HuEvolutionFormula.Named("LinearMap", c, HuEvolutionFormula.Coord(d), HuEvolutionFormula.Coord(d))))),
                    "Multiplication is complex bilinear. Associativity and a unit are not assumed."),
                HuEvolutionFormula.Def(Prefix, "square", "Span of all pair products",
                    HuEvolutionFormula.All("d", nat, HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d),
                        HuEvolutionFormula.All("U", HuEvolutionFormula.Sub(d),
                            HuEvolutionFormula.Eq(HuEvolutionFormula.Square(mu, F.Id("U")),
                                HuEvolutionFormula.Named("span", c, new Formula.SetBuilder(
                                    HuEvolutionFormula.Call(mu, F.Id("x"), F.Id("y")),
                                    Seq(Open, F.Id("x"), Comma, F.Id("y"), Close),
                                    Seq(F.Id("U"), Sp, Times, Sp, F.Id("U")))))))),
                    "The span includes every product of two elements of U; U need not be an ideal or a coordinate subspace."),
                HuEvolutionFormula.Def(Prefix, "commutative", "Commutativity",
                    HuEvolutionFormula.All("d", nat, HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d),
                        HuEvolutionFormula.Iff(HuEvolutionFormula.Comm(mu),
                            HuEvolutionFormula.All("x", HuEvolutionFormula.Coord(d),
                                HuEvolutionFormula.All("y", HuEvolutionFormula.Coord(d),
                                    HuEvolutionFormula.Eq(HuEvolutionFormula.Call(mu, F.Id("x"), F.Id("y")),
                                        HuEvolutionFormula.Call(mu, F.Id("y"), F.Id("x")))))))),
                    "This source hypothesis is retained explicitly, although the dimension-bound proof does not use it."),
                HuEvolutionFormula.Def(Prefix, "perfect", "Perfectness",
                    HuEvolutionFormula.All("d", nat, HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d),
                        HuEvolutionFormula.Iff(HuEvolutionFormula.Perfect(mu),
                            HuEvolutionFormula.Eq(HuEvolutionFormula.Square(mu, HuEvolutionFormula.Top), HuEvolutionFormula.Top)))),
                    "Perfectness means that pair products span the entire intrinsic coordinate space."),
                HuEvolutionFormula.Def(Prefix, "hasNaturalBasis", "An actual natural basis", NaturalFormula(),
                    "A basis has zero products between every pair of distinct basis vectors. Its squares may be dependent."),
                HuEvolutionFormula.Def(Prefix, "hasEvolutionEmbedding", "An actual evolution embedding", EmbeddingFormula(),
                    "The witness includes a bilinear ambient multiplication, its natural basis and an injective complex-linear map preserving every pair product."),
                Describe.Lean(DescribeId.Create("square-zero-dimension-bound"),
                    DeclarationHandle.Create(Prefix + "square_zero_embedding_lower_bound"), H("The general dimension bound"),
                    StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(
                        LibraryNoteRef.Create("D5/L/QuadraticForms/hu2026idempotent"),
                        LibraryNoteRef.Create("D5/L/QuadraticForms/costoya2026commutative")),
                    Blocks(
                        Paragraph(Text("The bound and argument are credited to Wenlin Zhang and Haobo Ma, Structure tests for stable derived terms. "
                            + "Hu and Wen supply the stable-derived-term setting; Costoya, Fernández Ouaridi and Viruel supply related evolution-envelope methods. No priority claim is made.")),
                        Paragraph(Text("In natural ambient coordinates write the product as M(x times y), with coordinatewise multiplication. "
                            + "Perfectness puts the embedded d-dimensional space into the range of M. Choose a vector in the embedded square-zero subspace "
                            + "that is nonzero on every coordinate appearing in its support. Such a vector exists over the infinite field of complex numbers, "
                            + "because finitely many proper coordinate kernels cannot cover the subspace. Coordinatewise multiplication by that vector is injective "
                            + "on the subspace, and its image lies in the kernel of M. Rank-nullity gives d plus finrank W at most n.")),
                        Paragraph(Text("The bound holds for every complex linear W, including W equal to zero, and for d equal to zero. "
                            + "It assumes neither ideal nor hyperplane status for W, and does not require the ambient evolution algebra to be perfect."))), DescribeRole.Theorem)), []));
    }
    private static Formula NaturalFormula()
    {
        var d=F.Id("d"); var mu=F.Id("mu"); var b=F.Id("b");
        return Disp(HuEvolutionFormula.All("d", HuEvolutionFormula.N, HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d),
            HuEvolutionFormula.Iff(HuEvolutionFormula.NatBasis(mu),
                HuEvolutionFormula.Some("b", HuEvolutionFormula.Named("Basis", HuEvolutionFormula.Fin(d), HuEvolutionFormula.C, HuEvolutionFormula.Coord(d)),
                    HuEvolutionFormula.All("i", HuEvolutionFormula.Fin(d), HuEvolutionFormula.All("j", HuEvolutionFormula.Fin(d),
                        HuEvolutionFormula.Imp(HuEvolutionFormula.Ne(F.Id("i"), F.Id("j")),
                            HuEvolutionFormula.Eq(HuEvolutionFormula.Call(mu, HuEvolutionFormula.Call(b,F.Id("i")), HuEvolutionFormula.Call(b,F.Id("j"))),D(0))))))))));
    }
    private static Formula EmbeddingFormula()
    {
        var d=F.Id("d"); var n=F.Id("n"); var mu=F.Id("mu"); var nu=F.Id("nu"); var f=F.Id("f");
        return Disp(HuEvolutionFormula.All("d", HuEvolutionFormula.N, HuEvolutionFormula.All("n", HuEvolutionFormula.N,
            HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d), HuEvolutionFormula.Iff(HuEvolutionFormula.Emb(mu,n),
                HuEvolutionFormula.Some("nu", HuEvolutionFormula.Product(n), HuEvolutionFormula.Some("f", HuEvolutionFormula.Linear(d,n),
                    HuEvolutionFormula.EmbData(d,nu,f,mu))))))));
    }
    private static Formula BoundFormula()
    {
        var d=F.Id("d"); var n=F.Id("n"); var mu=F.Id("mu"); var w=F.Id("W");
        return Disp(HuEvolutionFormula.All("d", HuEvolutionFormula.N, HuEvolutionFormula.All("n", HuEvolutionFormula.N,
            HuEvolutionFormula.All("mu", HuEvolutionFormula.Product(d), HuEvolutionFormula.All("W", HuEvolutionFormula.Sub(d),
                HuEvolutionFormula.Imp(HuEvolutionFormula.Comm(mu), HuEvolutionFormula.Imp(HuEvolutionFormula.Perfect(mu),
                    HuEvolutionFormula.Imp(HuEvolutionFormula.Eq(HuEvolutionFormula.Square(mu,w), HuEvolutionFormula.Bot),
                        HuEvolutionFormula.Imp(HuEvolutionFormula.Emb(mu,n), HuEvolutionFormula.Le(
                            HuEvolutionFormula.Add(d,HuEvolutionFormula.Named("finrank",HuEvolutionFormula.C,w)),n))))))))));
    }
}
