using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using SF = StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximumFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class EvolutionAutomorphismMaximumFormula
{
    internal static Formula V(string s) => F.Id(s);
    internal static Formula Call(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [..a]);
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula N => Seq(Mathbb,Grp(F.Id("N")));
    internal static Formula C => Seq(Mathbb,Grp(F.Id("C")));
    internal static Formula Type => V("Type");
    internal static Formula Card(Formula a) => Call("NatCard",a);
    internal static Formula Aut(Formula mu) => Call("Aut",mu);
    internal static Formula Coord(Formula n) => Call("Coord",n);
    internal static Formula Product(Formula n) => Call("Product",n);
    internal static Formula Maximum(Formula n) => Call("maximumWeight",n);
    internal static DocumentBlock.Describe Desc(string prefix,string name,string title,Formula f,string text,
        DescribeRole role=DescribeRole.Theorem,AssessedProvenance? provenance=null,OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role,
            openProblemResolutionClaim:resolution);
}

internal sealed class EvolutionAutomorphismMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.";
    private static Formula Universal(Formula n)
    {
        var a=SF.V("A");var i=SF.V("I");var mu=SF.V("mu");var b=SF.V("b");
        return SF.All("A",SF.Type,SF.Imp(SF.Call("FiniteDimensionalComplexVectorSpace",a),
            SF.All("I",SF.Type,SF.Imp(SF.Call("Fintype",i),
            SF.Imp(SF.Eq(SF.Call("finrank",a),n),SF.All("mu",SF.Call("BilinearProduct",a),
            SF.All("b",SF.Call("Basis",i,SF.C,a),SF.Imp(SF.Call("NaturalBasisAt",mu,b),
            SF.Imp(SF.Eq(SF.Call("productSpan",mu),SF.V("Top")),SF.And(SF.Call("Finite",SF.Aut(mu)),
                SF.Le(SF.Card(SF.Aut(mu)),SF.Maximum(n))))))))))));
    }
    private static Formula Attainment(Formula n)
    {
        var mu=SF.V("mu");
        return SF.Some("mu",SF.Product(n),SF.And(SF.Eq(SF.Call("finrank",SF.Coord(n)),n),
            SF.And(SF.Call("commutative",mu),SF.And(SF.Call("hasNaturalBasis",mu),
            SF.And(SF.Eq(SF.Call("productSpan",mu),SF.V("Top")),
            SF.And(SF.Call("Finite",SF.Aut(mu)),SF.Eq(SF.Card(SF.Aut(mu)),SF.Maximum(n))))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The partition weight is the attained maximum of the full automorphism orders of perfect complex evolution algebras in every positive finite dimension.",
        H("The full automorphism maximum"),Blocks(
            Paragraph(Text("Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1, section 2.3, Conjecture 3, pages 27-28, conjecture that the maximum order in dimension n is "
                + "the maximum over all multiplicities m_l with sum_l l m_l=n of product_l [l(2^l-1)]^(m_l) m_l!. The source states the attaining cyclic examples, and reports the upper bound checked only for n<=4. "
                + "The assertion is conjectural in that source; the universal proof below is a separate result. No global priority claim is made.")),
            SF.Desc(Prefix,"result","The universal bound and actual attainment",
                SF.All("n",SF.N,SF.Imp(SF.Le(D(1),SF.V("n")),SF.And(Universal(SF.V("n")),Attainment(SF.V("n"))))),
                "For every positive n, every arbitrary complex module of finrank n with any finite natural basis and with all pair products spanning the module has a finite full multiplication-preserving LinearEquiv group of order at most maximumWeight(n). "
                + "For the same n there exists an actual commutative, perfect bilinear evolution product on Fin(n) to C, whose finrank is exactly n, with a natural basis and full automorphism order equal to maximumWeight(n). "
                + "Associativity and a unit are never assumed. The bound retains all quotient fibers and their internal kernel. The attaining product sends e_i squared to e_(sigma(i)). "
                + "Choose the identity for n=1 and every n>=7; one cycle of lengths 2, 3, and 5 in those dimensions; two 2-cycles in dimension 4; three 2-cycles in dimension 6. "
                + "The exact full-group count follows from the constructed kernel and centralizer lifts. The existing arithmetic theorem gives the values 1, 6, 21, 72, 155, 1296 and n! for n>=7. "
                + "The witnesses establish a maximum rather than merely an upper bound or a supremum. No realization of every integer partition is needed.",
                provenance:AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution")),
                resolution:new OpenProblemResolutionClaim(ProblemSlugRef.Create("kaygorodov-martin-gonzalez-viruel-2026-evolution-automorphism-maximum"),ResolutionKind.Proved))),[]));
}
