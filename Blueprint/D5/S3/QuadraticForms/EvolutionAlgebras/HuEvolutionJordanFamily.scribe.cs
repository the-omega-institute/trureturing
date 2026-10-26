using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFormula;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class HuEvolutionJordanFormula
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

internal sealed class HuEvolutionJordanFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.";
    public DocumentDefinition Create()
    {
        var m=V("m"); var d=Add(m,D(1)); var mu=V("mu"); var n=V("n");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every positive Jordan-block family member is minimal perfect, lacks a natural basis and attains its exact evolution embedding dimension.",
            H("Minimal perfect Jordan-block algebras"), Blocks(
                Def(Prefix,"minimalPerfect","Minimality among all complex subspaces",
                    All("d",N,All("mu",Product(V("d")),Iff(Named("minimalPerfect",mu),
                        And(Perfect(mu),All("U",Sub(V("d")),Imp(Ne(V("U"),Bot),
                            Imp(Eq(Square(mu,V("U")),V("U")),Eq(V("U"),Top)))))))),
                    "Every nonzero complex linear subspace is included, rather than just ideals or coordinate spans."),
                Def(Prefix,"isEmbeddingDimension","Attained minimal dimension",
                    All("d",N,All("mu",Product(V("d")),All("n",N,Iff(Named("isEmbeddingDimension",mu,n),
                        And(Emb(mu,n),All("q",N,Imp(Emb(mu,V("q")),Le(n,V("q"))))))))),
                    "The first conjunct provides an actual embedding. The second bounds every possible ambient dimension."),
                Def(Prefix,"hasStableSquareEmbedding","Both stable-square equalities",StableFormula(),
                    "The witnesses are an actual bilinear evolution law and an injective complex-linear multiplication-preserving map. "
                    + "Both the square of the ambient space and the square of the embedded range equal that range."),
                Def(Prefix,"jordanProduct","The source coordinate law",ProductFormula(),
                    "Coordinate zero is u, and coordinate i is wi for 1 through m. For m at least one: "
                    + "u squared is 4u plus 2wm; uwi and wiu are 2wi plus 2w(i−1); wiwj is zero, with w0 zero. "
                    + "The next coordinate is evaluated only in the branch where its integer index is in range. The conditional formula also defines the dimension-one induction base without making a no-natural-basis claim there."),
                Def(Prefix,"jordanLaw","Equality with the source law",
                    All("m",N,All("mu",Product(d),Iff(Named("jordanLaw",m,mu),
                        All("x",Coord(d),All("y",Coord(d),Eq(Call(mu,V("x"),V("y")),Named("jordanProduct",m,V("x"),V("y")))))))),
                    "This is equality on all pairs of coordinate vectors, not just a table asserted without bilinearity."),
                Def(Prefix,"jordan","The bilinear implementation",
                    All("m",N,All("x",Coord(d),All("y",Coord(d),Eq(Call(Named("jordan",m),V("x"),V("y")),
                        Named("jordanProduct",m,V("x"),V("y")))))),
                    "The Lean construction supplies the four linearity proofs needed to inhabit Product(m+1)."),
                Def(Prefix,"coordinateProduct","A linear structure map defines an evolution product",
                    All("n",N,All("M",Linear(n,n),All("x",Coord(n),All("y",Coord(n),
                        Eq(Call(Named("coordinateProduct",V("M")),V("x"),V("y")),
                            Call(V("M"),Mul(V("x"),V("y")))))))),
                    "For any complex linear structure map M, multiply coordinates first and then apply M. This gives a bilinear product with zero mixed standard-basis products."),
                Describe.Lean(DescribeId.Create("coordinate-product-natural"),DeclarationHandle.Create(Prefix+"coordinate_product_natural"),
                    H("The standard coordinate law has a natural basis"),StatementSource.FromAuthor(Disp(
                        All("n",N,All("M",Linear(n,n),NatBasis(Named("coordinateProduct",V("M"))))))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The coordinate basis is natural for every linear structure map: the coordinatewise product of distinct coordinate vectors is zero."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("coordinate-product-square"),DeclarationHandle.Create(Prefix+"coordinate_product_square"),
                    H("The entire product span is the structure-map range"),StatementSource.FromAuthor(Disp(
                        All("n",N,All("M",Linear(n,n),Eq(Square(Named("coordinateProduct",V("M")),Top),Named("range",V("M"))))))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Every pair product lies in range(M). Conversely each image of a coordinate vector is its square and these images span range(M). Thus invertible structure maps give perfect products."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("entire-jordan-family"),DeclarationHandle.Create(Prefix+"jordan_family"),
                    H("The complete positive family and its exact embedding dimension"),StatementSource.FromAuthor(FamilyFormula()),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuadraticForms/hu2026idempotent"),
                        LibraryNoteRef.Create("D5/L/QuadraticForms/cabrera2017threedimensional"),
                        LibraryNoteRef.Create("D5/L/QuadraticForms/costoya2026commutative")),
                    Blocks(
                        Paragraph(Text("The family and its realization are credited to Wenlin Zhang and Haobo Ma, Structure tests for stable derived terms. "
                            + "Related literature is Hu and Wen, arXiv:2609.25023v1; Cabrera Casado, Siles Molina and Velasco, arXiv:1701.07219v2; "
                            + "and Costoya, Fernández Ouaridi and Viruel, arXiv:2609.32784v1. The formalization makes no global priority claim.")),
                        Paragraph(Text("Left multiplication by u has invertible diagonal entries and a nilpotent shift, so products span the intrinsic space. "
                            + "For minimality, drop the first square-zero coordinate w1 and induct on m. A nonzero perfect subspace has a nonzero perfect image, "
                            + "which equals the quotient by induction. Lift u, then recover w1 by subtracting 4x from x squared in the smallest case, "
                            + "or by subtracting 2y from xy using a lifted w2. The subspace then contains the kernel and maps onto the quotient, so it is the whole space.")),
                        Paragraph(Text("Map intrinsic coordinates x to x0 followed by all x0+xi and all x0−xi. This is injective. "
                            + "An intrinsic coefficient map sends coordinatewise products of embedded vectors to their intrinsic product. "
                            + "Compose that coefficient map with the embedding to prescribe the ambient basis squares. Mixed standard-basis products vanish. "
                            + "Surjectivity of the coefficient map makes the entire ambient square equal the embedded range; perfectness and product preservation "
                            + "give the second stable-square equality.")),
                        Paragraph(Text("The square-zero hyperplane has rank m. The general lower bound therefore gives 2m+1 for every evolution embedding. "
                            + "The explicit construction attains it, and rules out an intrinsic natural basis whenever m is at least one. "
                            + "Jordan-block names a nilpotent block, not a Jordan algebra identity. Neither the general idempotent obstruction "
                            + "nor the general nilpotent/cyclic classification is assumed or proved here."))),DescribeRole.Theorem)),[]));
    }
    private static Formula StableFormula()
    {
        var d=V("d"); var n=V("n"); var mu=V("mu"); var nu=V("nu"); var f=V("f"); var range=Named("range",f);
        return Disp(All("d",N,All("mu",Product(d),All("n",N,Iff(Named("hasStableSquareEmbedding",mu,n),
            Some("nu",Product(n),Some("f",Linear(d,n),And(EmbData(d,nu,f,mu),
                And(Eq(Square(nu,Top),range),Eq(Square(nu,range),range))))))))));
    }
    private static Formula ProductFormula()
    {
        var m=V("m"); var d=Add(m,D(1)); var x=V("x"); var y=V("y"); var k=V("k"); var r=Named("val",k);
        var xz=Call(x,D(0)); var yz=Call(y,D(0)); var xk=Call(x,k); var yk=Call(y,k); var next=Add(r,D(1));
        Formula Term(Formula a,Formula b) => Mul(Mul(D(2),a),b);
        var shift=Named("ite",Lt(next,d),Add(Term(xz,Call(y,next)),Term(Call(x,next),yz)),D(0));
        var last=Named("ite",Eq(r,m),Term(xz,yz),D(0));
        var tail=Add(Add(Add(Term(xz,yk),Term(xk,yz)),shift),last);
        return Disp(All("m",N,All("x",Coord(d),All("y",Coord(d),All("k",Fin(d),
            Eq(Call(Named("jordanProduct",m,x,y),k),Named("ite",Eq(r,D(0)),Mul(Mul(D(4),xz),yz),tail)))))));
    }
    private static Formula FamilyFormula()
    {
        var m=V("m"); var d=Add(m,D(1)); var mu=V("mu"); var n=Add(Mul(D(2),m),D(1));
        return Disp(All("m",N,Imp(Le(D(1),m),Some("mu",Product(d),And(Named("jordanLaw",m,mu),
            And(Comm(mu),And(Named("minimalPerfect",mu),And(new Formula.Not(NatBasis(mu)),
                And(Named("hasStableSquareEmbedding",mu,n),Named("isEmbeddingDimension",mu,n))))))))));
    }
}
