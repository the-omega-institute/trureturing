using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Heisenberg;

internal sealed class HeisenbergCommutingGraphDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Heisenberg/CommutingGraph.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/arvind2023commuting");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full commuting graphs use whole-element distinctness, and source-derived groups use the inverse-first commutator.",
        H("The full graph and source convention"), Blocks(
            Describe.Lean(DescribeId.Create("full-commuting-graph"), DeclarationHandle.Create(Owner + "commutingGraph"),
                H("All elements are vertices"), StatementSource.FromAuthor(Disp(Graph())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The vertex type is the entire group G. Adjacency is the conjunction x distinct from y and x*y=y*x. In particular the identity and every centre element are retained. The simple graph has no loops; distinct elements that differ only in a central coordinate remain eligible for adjacency."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-isoclinism"), DeclarationHandle.Create(Owner + "Isoclinic"),
                H("Isoclinism intertwines the source commutators"), StatementSource.FromAuthor(Disp(Isoclinism())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("sourceCommutator(x,y) is x inverse times y inverse times x times y. sourceDerived is the subgroup closure of all these commutators. Isoclinic G H asserts the existence of a group isomorphism a from G modulo its centre to H modulo its centre and a group isomorphism b of the source derived subgroups. For every x,y in G and every u,v in H representing a(xZ(G)) and a(yZ(G)), the image under b of sourceCommutator(x,y) equals sourceCommutator(u,v). The commutator is coerced into the ambient group in this equality. This retains compatibility for all representatives, rather than comparing derived groups alone."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-derived-axis"), DeclarationHandle.Create(Owner + "sourceDerived_axis"),
                H("The source derived subgroup is the same axis"), StatementSource.FromAuthor(Disp(All("A",Call("Type"),Inst("CommRing",F.Id("A"),
                    Eq(Call("sourceDerived",Call("HeisenbergGroup",F.Id("A"))),Call("zAxis",F.Id("A"))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary groups sourceCommutator(x,y) is the native commutator of x inverse and y inverse. Inversion of both generators is bijective, so the two generating sets and their subgroup closures agree. Applying the generic Heisenberg derived-axis theorem gives the displayed source-convention equality. The proof does not assert that the two commutator words are definitionally equal on the original pair."))), DescribeRole.Theorem),
            Paragraph(Text("liftGraphIso accepts an actual bijection of the two-coordinate bases preserving equality of cross products and a bijection of the coefficient carriers. Their product transports all triples bijectively. Equality of cross products is equivalent to commutation of triples. Bijectivity separately preserves inequality of the whole triples. This establishes graph isomorphism without removing centres or requiring bases to be distinct.")))));
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Par(Formula a) => Seq(Open,a,Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Inst(string n, Formula t, Formula b) => Seq(OpenBracket,Call(n,t),CloseBracket,Sp,b);
    private static Formula Graph()
    {
        var g=F.Id("G");var x=F.Id("x");var y=F.Id("y");
        return All("G",Call("Type"),Inst("Group",g,All("x",g,All("y",g,
            Eq(Call("Adj",Call("commutingGraph",g),x,y),And(new Formula.Relation(x,FormulaRelationOperator.NotEqual,y),Eq(Call("mul",x,y),Call("mul",y,x))))))));
    }
    private static Formula Isoclinism()
    {
        var g=F.Id("G");var h=F.Id("H");var a=F.Id("a");var b=F.Id("b");
        var x=F.Id("x");var y=F.Id("y");var u=F.Id("u");var v=F.Id("v");
        return All("G",Call("Type"),All("H",Call("Type"),Inst("Group",g,Inst("Group",h,
            Eq(Call("Isoclinic",g,h),Ex("a",Call("MulEquiv",Call("CentralQuotient",g),Call("CentralQuotient",h)),
                Ex("b",Call("MulEquiv",Call("sourceDerived",g),Call("sourceDerived",h)),
                    All("x",g,All("y",g,All("u",h,All("v",h,
                        Imp(Eq(Call("apply",a,Call("Coset",x)),Call("Coset",u)),
                            Imp(Eq(Call("apply",a,Call("Coset",y)),Call("Coset",v)),
                                Eq(Call("apply",b,Call("sourceCommutator",x,y)),Call("sourceCommutator",u,v)))))))))))))));
    }
}
