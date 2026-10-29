using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamilyFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class EvolutionPermutationFamilyFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [..a]);
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula N => Seq(Mathbb,Grp(F.Id("N")));
    internal static Formula Card(Formula a) => Call("NatCard",a);
    internal static Formula Aut(Formula mu) => Call("Aut",mu);
    internal static Formula Coord(Formula n) => Call("Coord",n);
    internal static Formula Perm(Formula q) => Call("Perm",q);
    internal static Formula Parts(Formula sigma) => Call("parts",Call("partition",sigma));
    internal static Formula Weight(Formula p) => Call("weight",p);
    internal static Formula Index(Formula n) => Call("Fin",n);
    internal static Formula PermContext(Formula f) => All("n",N,All("sigma",Perm(Index(V("n"))),f));
    internal static DocumentBlock.Describe Desc(string prefix,string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem,AssessedProvenance? provenance=null,OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role,
            openProblemResolutionClaim:resolution);
}

internal sealed class EvolutionPermutationFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.";
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution"));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula BasisVector(Formula n,Formula i) => App(
        new Formula.Apply(Seq(Operatorname,Grp(F.Id("Pi")),Dot,Operatorname,Grp(F.Id("basisFun"))),
            [SF.V("Complex"),SF.Index(n)]),i);
    private static Formula MixedStatement(Formula n,Formula mu) => SF.PermContext(
        SF.All("i",SF.Index(n),SF.All("j",SF.Index(n),new Formula.Logic(
            new Formula.Relation(SF.V("i"),FormulaRelationOperator.NotEqual,SF.V("j")),
            FormulaLogicOperator.Implies,SF.Eq(App(mu,BasisVector(n,SF.V("i")),BasisVector(n,SF.V("j"))),D(0))))));
    public DocumentDefinition Create()
    {
        var n=SF.V("n");var sigma=SF.V("sigma");var tau=SF.V("tau");var x=SF.V("x");var y=SF.V("y");
        var mu=SF.Call("permutationProduct",sigma);
        Formula Apply(Formula f,Formula z)=>SF.Call("apply",f,z);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Coefficient-one permutation evolution algebras realize the complete root kernel and permutation centralizer.",
            H("Attaining permutation algebras"),Blocks(
                SF.Desc(Prefix,"permutationLinear","The coordinate permutation",SF.PermContext(SF.All("x",SF.Coord(n),
                    SF.All("j",SF.Index(n),SF.Eq(SF.Call("coordinate",Apply(SF.Call("permutationLinear",sigma),x),SF.V("j")),
                        SF.Call("coordinate",x,SF.Call("inverseApply",sigma,SF.V("j"))))))),
                    "The linear equivalence P_sigma sends coordinate vector e_i to e_(sigma(i)); its j-th output coordinate is x_(sigma inverse(j)).",DescribeRole.Definition),
                SF.Desc(Prefix,"permutationProduct","The bilinear evolution law",SF.PermContext(SF.All("x",SF.Coord(n),SF.All("y",SF.Coord(n),
                    SF.Eq(SF.Call("ApplyProduct",mu,x,y),Apply(SF.Call("permutationLinear",sigma),SF.Mul(x,y)))))),
                    "The product is P_sigma applied to coordinatewise multiplication. The original coordinateProduct construction supplies bilinearity. "
                    + "Its basis squares are e_i squared=e_(sigma(i)) and distinct basis vectors multiply to zero. The structure map is invertible, so all pair products span the whole space.",DescribeRole.Definition,Source),
                SF.Desc(Prefix,"permutationLinear_basis","The image of each coordinate basis vector",SF.PermContext(
                    SF.All("i",SF.Index(n),SF.Eq(App(SF.Call("permutationLinear",sigma),BasisVector(n,SF.V("i"))),
                        BasisVector(n,App(sigma,SF.V("i")))))),
                    "For every n, permutation sigma and index i, permutationLinear sigma sends Pi.basisFun at i to Pi.basisFun at sigma(i). This identity identifies the support permutation of explicit automorphisms."),
                SF.Desc(Prefix,"permutation_mixed","Products of distinct basis vectors vanish",MixedStatement(n,mu),
                    "For every n, permutation sigma and distinct i,j in Fin n, permutationProduct sigma applied to the two coordinate basis vectors is zero. This supplies the natural basis for the cyclic algebras."),
                SF.Desc(Prefix,"permutation_support","The exact support relation",SF.PermContext(
                    SF.All("i",SF.Index(n),SF.All("j",SF.Index(n),new Formula.Logic(
                        SF.Call("supportRelation",mu,new Formula.Apply(Seq(Operatorname,Grp(F.Id("Pi")),Dot,Operatorname,Grp(F.Id("basisFun"))),
                            [SF.V("Complex"),SF.Index(n)]),SF.V("i"),SF.V("j")),
                        FormulaLogicOperator.Iff,SF.Eq(SF.V("j"),App(sigma,SF.V("i"))))))),
                    "For every n, permutation sigma and indices i,j, the supportRelation of permutationProduct sigma in Pi.basisFun has an arrow from i to j exactly when j=sigma(i). The cyclic family uses this to establish strong connectivity."),
                SF.Desc(Prefix,"centralizerLift","Every commuting permutation lifts",SF.PermContext(
                    SF.All("tau",SF.Call("centralizer",sigma),SF.Call("Member",SF.Call("centralizerLift",sigma,tau),SF.Aut(mu)))),
                    "For each tau commuting with sigma, P_tau preserves the product on all vector pairs. It is therefore an actual member of the full LinearEquiv automorphism group. "
                    + "Its support permutation is tau itself. These explicit lifts prove equality of the actual projection image and the full centralizer.",DescribeRole.Definition,Source),
                SF.Desc(Prefix,"permutation_aut_card","Exact full-group cardinality",SF.PermContext(
                    SF.And(SF.Call("Finite",SF.Aut(mu)),SF.Eq(SF.Card(SF.Aut(mu)),SF.Weight(SF.Parts(sigma))))),
                    "The entire algebra group is finite. Monomiality identifies its actual permutation image; preservation of basis squares forces that image to commute with sigma, and the lifts prove the converse inclusion. "
                    + "The actual kernel is exactly the unit assignments a_(sigma(i))=a_i squared. Existing independent cycle-root realization counts it, including the singleton root factor one. "
                    + "Kernel cardinality times image cardinality is therefore the full partition weight, with every singleton multiplicity factorial retained. "
                    + "The source states attainment by sums of cyclic algebras; this proof derives the exact cardinality directly without assuming a wreath-product classification.",provenance:Source),
                SF.Desc(Prefix,"permutation_family","All algebraic witness conditions",SF.PermContext(
                    SF.And(SF.Call("commutative",mu),SF.And(SF.Call("hasNaturalBasis",mu),SF.And(SF.Call("perfect",mu),
                        SF.And(SF.Call("Finite",SF.Aut(mu)),SF.Eq(SF.Card(SF.Aut(mu)),SF.Weight(SF.Parts(sigma)))))))),
                    "Every permutation gives a commutative, perfect complex evolution algebra on Fin(n) to C. It need not be associative. "
                    + "Naturality and perfection use the original coordinate-product facts. The same actual algebra and same full automorphism group satisfy the exact order formula.",provenance:Source)),[]));
    }
}
