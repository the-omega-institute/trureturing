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
    private static Formula Apply(Formula f,params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Qualified(string owner,string name) => Seq(Operatorname,Grp(F.Id(owner)),Dot,Operatorname,Grp(F.Id(name)));
    private static Formula Instance(Formula t,Formula body) => Seq(OpenBracket,t,CloseBracket,Sp,body);
    private static Formula NaturalAt(Formula index,Formula basis) => SF.All("i",index,SF.All("j",index,
        SF.Imp(new Formula.Relation(SF.V("i"),FormulaRelationOperator.NotEqual,SF.V("j")),
            SF.Eq(Apply(Mu,Apply(basis,SF.V("i")),Apply(basis,SF.V("j"))),D(0)))));
    private static Formula ReindexedNatural()
    {
        var complex=SF.V("Complex");var i=SF.V("I");var n=SF.V("n");
        var type = Seq(Operatorname, Grp(F.Id("Type")));
        var reindexed=SF.Call("dimensionBasis",SF.V("hn"),Basis);
        return SF.All("A",type,Instance(SF.Call("AddCommGroup",A),Instance(SF.Call("Module",complex,A),
            Instance(SF.Call("FiniteDimensional",complex,A),SF.All("I",type,Instance(SF.Call("Fintype",i),
                SF.All("n",SF.V("Nat"),SF.All("hn",SF.Eq(Apply(Qualified("Module","finrank"),complex,A),n),
                    SF.All("mu",SF.Call("LinearMap",complex,A,SF.Call("LinearMap",complex,A,A)),
                        SF.All("b",Apply(Qualified("Module","Basis"),i,complex,A),
                            SF.Imp(NaturalAt(i,Basis),NaturalAt(SF.Call("Fin",n),reindexed))))))))))));
    }
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
                Desc("dimensionBasis_natural","Reindexing preserves zero mixed products",ReindexedNatural(),
                    "Let A be a finite-dimensional complex vector space, I a finite index type, hn an equality finrank(A)=n, mu a bilinear product and b an I-indexed basis. "
                    + "If mu(b(i),b(j))=0 for distinct I-indices, the same is true of dimensionBasis hn b for distinct Fin n indices. Injectivity of the reindexing equivalence preserves distinctness. "
                    + "The arbitrary-module automorphism bound uses this to apply the coordinate theorem."),
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
