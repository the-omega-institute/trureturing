using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionTransportFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class EvolutionTransportFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    internal static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Type => V("Typeu");
    internal static Formula Card(Formula t) => Call("card", t);
}

internal sealed class EvolutionBasisTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport.";
    private static Formula A => SF.V("A");
    private static Formula B => SF.V("B");
    private static Formula Mu => SF.V("mu");
    private static Formula E => SF.V("e");
    private static Formula Basis => SF.V("b");
    private static Formula Nu => SF.Call("transportProduct",E,Mu);
    private static Formula Aut(Formula p) => SF.Call("Aut",p);
    private static Formula TransportContext(Formula f) => SF.All("A",SF.Type,SF.All("B",SF.Type,
        SF.Imp(SF.Call("ComplexVectorSpace",A),SF.Imp(SF.Call("ComplexVectorSpace",B),
            SF.All("e",SF.Call("LinearEquiv",A,B),SF.All("mu",SF.Call("BilinearProduct",A),f))))));
    private static Formula BasisContext(Formula f) => SF.All("A",SF.Type,
        SF.Imp(SF.Call("FiniteDimensionalComplexVectorSpace",A),
            SF.All("I",SF.Type,SF.Imp(SF.Call("Fintype",SF.V("I")),
                SF.All("n",SF.Call("NaturalNumbers"),
                    SF.Imp(SF.Eq(SF.Call("finrank",A),SF.V("n")),
                        SF.All("mu",SF.Call("BilinearProduct",A),
                            SF.All("b",SF.Call("Basis",SF.V("I"),SF.V("Complex"),A),
                                SF.Imp(SF.Call("NaturalBasisAt",Mu,Basis),
                                    SF.Imp(SF.Eq(SF.Call("productSpan",Mu),SF.V("Top")),f))))))))));
    private static DocumentBlock.Describe Desc(string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
    public DocumentDefinition Create()
    {
        var r=SF.Call("SupportOfCoordinateProduct",Mu,Basis,SF.V("n"));
        var beta=SF.Call("beta",r);
        return DocumentDefinition.Create(ScribeNode.Create(
            "All multiplication automorphisms of an arbitrary finite-dimensional perfect complex evolution algebra obey joint cycle, quotient and block control.",
            H("Basis transport and the full algebra group"),Blocks(
                EvolutionBasisTransportPublication.Node("dimensionBasis_natural", EvolutionBasisTransportPublication.Naturality(), "Reindexing a finite natural basis by its dimension preserves every zero mixed product."),

                Paragraph(Text("A and B are complex vector spaces with bilinear multiplication mu. Neither associativity nor a multiplicative unit is required. "
                    + "productSpan(mu) is the span of every mu(x,y); perfection means productSpan(mu)=Top. "
                    + "The automorphism group is the single Aut definition of EvolutionAutomorphismControl: all complex LinearEquivs preserving every pair product.")),
                Desc("transportProduct","Transporting the multiplication",TransportContext(
                    SF.All("x",B,SF.All("y",B,SF.Eq(SF.Call("ApplyProduct",Nu,SF.V("x"),SF.V("y")),
                        SF.Call("e",SF.Call("ApplyProduct",Mu,SF.Call("inverse",E,SF.V("x")),SF.Call("inverse",E,SF.V("y")))))))),
                    "For x,y in B, the transported multiplication is e(mu(e inverse(x),e inverse(y))). Bilinearity follows from composition of linear maps.",DescribeRole.Definition),
                Desc("product_span_transport","Exact product-span correspondence",TransportContext(
                    SF.Eq(SF.Call("map",E,SF.Call("productSpan",Mu)),SF.Call("productSpan",Nu))),
                    "The image under e of the span of all pair products is exactly the span of all transported pair products. "
                    + "Surjectivity of e supplies the reverse inclusion. Since e has zero kernel and full range, perfection is equivalent on the two spaces."),
                Desc("automorphismConjugacy","Conjugacy of the entire automorphism group",TransportContext(
                    SF.Call("GroupEquiv",Aut(Mu),Aut(Nu))),
                    "The map sends f to e composed with f composed with e inverse. Its inverse conjugates by e inverse. "
                    + "Both maps preserve multiplication because the transported product is defined on all pairs. They are inverse group homomorphisms; "
                    + "no monomiality, support lift, finiteness or conjugacy premise is inserted.",DescribeRole.Definition),
                Desc("natural_basis_transport_iff","The natural-basis correspondence",
                    SF.All("A",SF.Type,SF.Imp(SF.Call("ComplexVectorSpace",A),SF.All("n",SF.V("NaturalNumbers"),
                        SF.All("mu",SF.Call("BilinearProduct",A),SF.All("b",SF.Call("Basis",SF.Call("Fin",SF.V("n")),SF.V("Complex"),A),
                            SF.And(SF.Imp(SF.Call("NaturalBasisAt",Mu,Basis),SF.Call("CoordinateBasisNatural",Mu,Basis)),
                                SF.Imp(SF.Call("CoordinateBasisNatural",Mu,Basis),SF.Call("NaturalBasisAt",Mu,Basis)))))))),
                    "The equivalence b.equivFun sends b(i) to the i-th coordinate vector. Products of distinct basis vectors therefore vanish exactly "
                    + "when products of the corresponding coordinate basis vectors vanish."),
                Desc("dimensionBasis","The finite-index bridge",
                    SF.All("A",SF.Type,SF.Imp(SF.Call("FiniteDimensionalComplexVectorSpace",A),
                        SF.All("I",SF.Type,SF.Imp(SF.Call("Fintype",SF.V("I")),
                            SF.All("n",SF.Call("NaturalNumbers"),SF.Imp(SF.Eq(SF.Call("finrank",A),SF.V("n")),
                                SF.All("b",SF.Call("Basis",SF.V("I"),SF.V("Complex"),A),
                                    SF.Call("Basis",SF.Call("Fin",SF.V("n")),SF.V("Complex"),A)))))))),
                    "For any finite index type I and any basis b indexed by I, finrank equals card(I). Given finrank(A)=n, "
                    + "Fintype.equivFinOfCardEq and Basis.reindex produce the n-indexed basis. Its naturality follows by injectivity of the index equivalence. "
                    + "Thus the original natural basis is arbitrary, and the n-dimensional source quantifier is retained.",DescribeRole.Definition),
                Desc("finite_and_joint_bound","Joint control on the actual algebra group",BasisContext(
                    SF.And(SF.Call("Finite",Aut(Mu)),SF.Le(SF.Card(Aut(Mu)),
                        SF.Mul(SF.Mul(SF.Call("cycleWeight",beta),SF.Card(SF.Call("centralizer",beta))),SF.Call("BlockFactorialProduct",r))))),
                    "First transport along the reindexed basis and prove coordinate perfection and naturality. The coordinate algebra group is finite, "
                    + "and the group conjugacy transfers that actual finiteness before Nat.card is used. Let R be the support of the transported product, "
                    + "P its least successor-compatible quotient, beta the induced permutation, and B_q the original vertices in quotient class q. "
                    + "The bound is product_c(2^card(c)-1) times card(centralizer_Sym(P)(beta)) times product_q(card(B_q)!). "
                    + "The cycles c partition P, not the n original vertices. Singleton cycles contribute one. Exact diagonal assignment descent and cycle-root "
                    + "realization supply the first factor. The actual kernel of the block action injects into the product of the symmetric groups of B_q; "
                    + "it may be nontrivial. No support-surjectivity or faithful quotient-action hypothesis is used. The neutral n=0 case is included."),
                Paragraph(Text("This joint control concerns the full source family in Conjecture 3 of Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1. "
                    + "It does not assert the conjecture's sharp maximum or attainment. The partition maximum, six small dimensions, factorial tail and absorption, "
                    + "coefficient-one cyclic-family attainment, and final upper-bound-plus-attainment assembly remain further mathematical requirements."))),[]));
    }
}

internal static class EvolutionBasisTransportPublication
{

    internal static DocumentBlock.Describe Node(string name, Formula formula, string text) => Describe.Lean(
        DescribeId.Create("published-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport." + name), H(name),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula X(string s) => F.Id(s);
    private static Formula Name(string s) => Seq(Operatorname, Grp(X(s)));
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Call(string s, params Formula[] a) => App(Name(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, t)), Comma, Sp, Parenthesized(b));
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Complex => Seq(Mathbb, Grp(X("C")));
    private static Formula Natural => Seq(Mathbb, Grp(X("N")));
    private static Formula VectorContext(Formula a, Formula f) => All(a, Name("Type"), Instance(Call("AddCommGroup", a), Instance(Call("Module", Complex, a), f)));
    private static Formula Product(Formula k, Formula a) => Call("LinearMap", k, a, Call("LinearMap", k, a, a));
    private static Formula Basis(Formula k, Formula i, Formula a) => App(Q("Module", "Basis"), i, k, a);
    private static Formula Mixed(Formula mu, Formula b, Formula index) => All(X("i"), index, All(X("j"), index, Imp(Ne(X("i"), X("j")), Eq(App(mu, App(b, X("i")), App(b, X("j"))), D(0)))));

    internal static Formula Naturality()
    {
        var a=X("A"); var index=X("I"); var n=X("n"); var mu=X("mu"); var b=X("b");
        var bn=Call("dimensionBasis", X("hn"), b); var fin=Call("Fin", n);
        return VectorContext(a, Instance(Call("FiniteDimensional",Complex,a),
            All(index,Name("Type"),Instance(Call("Fintype",index),All(n,Natural,
                All(X("hn"),Eq(App(Q("Module","finrank"),Complex,a),n),
                    All(mu,Product(Complex,a),All(b,Basis(Complex,index,a),
                        Imp(Mixed(mu,b,index),Mixed(mu,bn,fin))))))))));
    }
}
