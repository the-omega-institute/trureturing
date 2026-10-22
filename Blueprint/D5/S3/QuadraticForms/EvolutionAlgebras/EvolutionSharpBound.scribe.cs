using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionMaximumFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class EvolutionMaximumFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [..a]);
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula N => Seq(Mathbb,Grp(F.Id("N")));
    internal static Formula C => Seq(Mathbb,Grp(F.Id("C")));
    internal static Formula Type => V("Type");
    internal static Formula Card(Formula a) => Call("NatCard",a);
    internal static Formula Aut(Formula mu) => Call("Aut",mu);
    internal static Formula Coord(Formula n) => Call("Coord",n);
    internal static Formula Product(Formula n) => Call("Product",n);
    internal static Formula Perm(Formula q) => Call("Perm",q);
    internal static Formula Parts(Formula sigma) => Call("parts",Call("partition",sigma));
    internal static Formula Weight(Formula p) => Call("weight",p);
    internal static Formula Maximum(Formula n) => Call("maximumWeight",n);
    internal static Formula Index(Formula n) => Call("Fin",n);
    internal static Formula Standard(Formula n) => Call("standardBasis",n);
    internal static Formula PermContext(Formula f) => All("n",N,All("sigma",Perm(Index(V("n"))),f));
    internal static Formula BasisContext(Formula f)
    {
        var a=V("A");var i=V("I");var n=V("n");var mu=V("mu");var basis=V("b");
        var body=Imp(Eq(Call("productSpan",mu),V("Top")),f);
        body=Imp(Call("NaturalBasisAt",mu,basis),body);
        body=All("b",Call("Basis",i,C,a),body);
        body=All("mu",Call("BilinearProduct",a),body);
        body=Imp(Eq(Call("finrank",a),n),body);
        body=Imp(Le(D(1),n),body);
        body=All("n",N,body);
        body=Imp(Call("Fintype",i),body);
        body=All("I",Type,body);
        body=Imp(Call("FiniteDimensionalComplexVectorSpace",a),body);
        return All("A",Type,body);
    }
    internal static DocumentBlock.Describe Desc(string prefix,string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem,AssessedProvenance? provenance=null,OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role,
            openProblemResolutionClaim:resolution);
}

internal sealed class EvolutionSharpBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.";
    public DocumentDefinition Create()
    {
        var beta=SF.V("beta"); var q=SF.V("Q"); var mu=SF.V("mu");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every positive-dimensional perfect complex evolution algebra has a finite full automorphism group bounded by the partition maximum.",
            H("The universal sharp upper bound"),Blocks(
                Paragraph(Text("The multiplication is a complex bilinear map on an arbitrary finite-dimensional complex vector space. A natural basis has zero products between distinct basis vectors. "
                    + "Perfection is the equality between the span of all pair products and the entire space. The group Aut contains every multiplication-preserving complex LinearEquiv; no associativity or unit is assumed.")),
                SF.Desc(Prefix,"cycle_weight_centralizer","The entire successor partition",
                    SF.All("Q",SF.Type,SF.Imp(SF.Call("Fintype",q),SF.Imp(SF.Call("DecidableEq",q),SF.All("beta",SF.Perm(q),
                        SF.Eq(SF.Mul(SF.Call("cycleWeight",beta),SF.Card(SF.Call("centralizer",beta))),SF.Weight(SF.Parts(beta))))))),
                    "A permutation beta on Q has the full partition consisting of its nontrivial cycle lengths and one singleton for every fixed point. "
                    + "The existing independent root count contributes product_l (2^l-1)^(m_l). The full centralizer contributes product_l l^(m_l) m_l!, "
                    + "including m_1!. Their product is exactly weight(partition(beta)). The centralizer normalization reuses the Tau Ceti multiplicity formula and Mathlib's cardinality theorem."),
                SF.Desc(Prefix,"finite_and_bound","The arbitrary-carrier bound",SF.BasisContext(
                    SF.And(SF.Call("Finite",SF.Aut(mu)),SF.Le(SF.Card(SF.Aut(mu)),SF.Maximum(SF.V("n"))))),
                    "For every finite natural basis indexed by an arbitrary finite type I, finrank(A)=n and n>=1, the whole group is finite and its natural cardinality is at most maximumWeight(n). "
                    + "Transport first gives the actual joint bound on the least support quotient P. Every original fiber has size k(B)>=1, their sizes sum to n, and s=card(P) lies between one and n. "
                    + "Ascending-factorial monotonicity bounds the product of the actual fiber factorials by (n-s+1)!. The successor cycles partition s, not n. "
                    + "Their root and centralizer factors form the weight of a full partition of s, bounded by maximumWeight(s). The existing shifted absorption estimate yields maximumWeight(n). "
                    + "The internal block-action kernel is retained throughout; neither a faithful quotient action nor surjectivity onto graph automorphisms is required."),
                Paragraph(Text("The upper bound is the universal inequality in Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1, section 2.3, Conjecture 3, pages 27-28. "
                    + "The published statement is conjectural. EvolutionAutomorphismMaximum combines this inequality with actual attaining algebras."))),[]));
    }
}
