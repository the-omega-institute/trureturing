using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;
internal sealed class HKNNResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/liwu2026j1j2rings");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The block Bloch state has strictly largest HKNN weight", H("The block Bloch state has strictly largest HKNN weight"), Blocks(
            Node("claim", "Li and Wu, p. 12, after Eq. (47): \"Thus, we conjecture that this property holds for arbitrary even number N, i.e., the Bloch state |ξ1,1,...,1(−π)⟩ (there are N/2 − 1 1’s) should have the largest weight in |ψHKNN(N)⟩.\". Eq. (6), p. 4: \"|ψHKNN⟩ = Σ_{aj<bj and a1<a2<···<aN/2} [a1, b1] · · · [aN/2, bN/2], (6)\"; \"where the sum is over all partitions of {1, 2, . . . , N} into pairs without regard to order.\" Singlet, p. 3: \"[i, j] ≡ | ↑⟩i | ↓⟩j − | ↓⟩i | ↑⟩j is a singlet state on sites i and j.\". Bloch normalization, p. 4, Eq. (7): \"|ξ1(k)⟩ = e^{ik/2}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 2⟩, |ξ2(k)⟩ = e^{ik}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 3⟩, |ξ3(k)⟩ = e^{i3k/2}/√3 Σ_{j=0}^{2} e^{ikj} T^j |1, 4⟩, (7)\". N=2m, m>=1; site i corresponds to paper site i+1. The middle index is the Fin (2*m) constructor value with natural value m and the bound m < 2*m supplied by m>=1; fin(m,2*m) displays that value. It carries pi=-pi. The exclusion removes the same block ray up to phase; every other nonzero Bloch state is compared strictly.", claimFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The block coefficient attains the crossing-pairing modulus. Every non-arc configuration has a strict deficit because interleaving partners can be swapped to reverse one sign. Translation selects the middle momentum, and the finite support estimate promotes coefficient maximality to strict normalized Bloch weight maximality.", resultFormula(), DescribeRole.Theorem, AssessedProvenance.FromRepo())
        ), []));
    private static DocumentBlock Node(string name, string prose, Formula formula, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hknn-settlement-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Exists(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula Negate(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Sites(Formula m) => Call("Fin", Mul(D(2), m));
    private static Formula Config(Formula m) => Call("Stationing", Mul(D(2), m));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Iterate(Formula m, Formula j, Formula x) => Call("iterate", Call("shift",m), j, x);
    private static Formula Index(Formula m) => Call("fin", m, Mul(D(2), m));
    private static Formula ClaimBody()
    {
        Formula m=F.Id("m"), x=F.Id("x"), t=F.Id("t"), j=F.Id("j");
        Formula arc=Exists("j",N(),Eq(x,Iterate(m,j,Call("block",m))));
        Formula rival=All("x",Config(m),All("t",Sites(m),Imp(Ne(Call("bloch",m,x,t),D(0)),
            Imp(Negate(And(arc,Eq(Val(t),m))),Lt(Call("weight",m,x,t),Call("weight",m,Call("block",m),Index(m)))))));
        return All("m",N(),Imp(Le(D(1),m),And(Ne(Call("bloch",m,Call("block",m),Index(m)),D(0)),rival)));
    }
    private static Formula claimFormula()
    {
        return new Formula.Logic(Named("claim"),FormulaLogicOperator.Iff,Parenthesized(ClaimBody()));
    }
    private static Formula resultFormula()
    {
        return ClaimBody();
    }
}
