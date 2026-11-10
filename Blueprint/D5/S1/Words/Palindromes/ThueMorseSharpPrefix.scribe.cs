using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class ThueMorseSharpPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/ThueMorseSharpPrefix.";
    private static readonly LibraryNoteRef Akmp = LibraryNoteRef.Create("D5/L/Words/ambrozetal2019palindromiclength");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp factor-two comparison of the actual ordinary and mixed minimum costs on every zero-start Thue-Morse prefix.",
        H("Sharp Factor Two for Thue-Morse Prefixes"), Blocks(
        Describe.Lean(DescribeId.Create("tm-prefix-signed-upper"), DeclarationHandle.Create(Prefix + "prefix_signed_upper"),
            H("An ordinary upper bound by signed weight"), StatementSource.FromAuthor(Disp(All("n", N(),
                Le(Pl(V("n")), Mul(D(2), Call("signedWeight", Call("int", V("n")))))))),
            AssessedProvenance.FromRepo(Akmp), Blocks(Paragraph(Text("Write P(n)=PL(factor(n,0)) and W(n)=signedWeight(int(n)). The existing substitution tau maps each letter b to [b,not b,not b,b], preserves palindromes, and gives P(4m)<=P(m). The one-letter Lipschitz inequality bounds both insertion and deletion. Signed-weight arithmetic gives W(4m)=W(m), W(4m+1)=W(m)+1, W(4m+2)=1+min(W(m),W(m+1)), and W(4m+3)=W(m+1)+1. Strong induction handles residues zero and one from 4m, residue three from 4(m+1), and residue two from both neighboring multiples of four. In the latter case the two available upper bounds are 2W(m)+2 and 2W(m+1)+2. The empty prefix has both P and W zero. This all-prefix estimate is used in sharp_factor_two_prefix, in both the universal bound and the native attainer proof."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("tm-sharp-factor-two-prefix"), DeclarationHandle.Create(Prefix + "sharp_factor_two_prefix"),
            H("The complete sharp comparison for actual minima"), StatementSource.FromAuthor(SharpFormula()),
            AssessedProvenance.FromRepo(Akmp), Blocks(Paragraph(Text("Section 6 and Table 1 of Ambroz, Kadlec, Masakova and Pelantova motivate the sharp factor-two comparison. The word is the literal zero-start prefix factor(n,0), with false=a and true=b. P is the minimum number of consecutive nonempty palindrome pieces. C=combinedLength minimizes consecutive nonempty pieces, each a palindrome or an exchange-reversal antipalindrome, on the same word. The existing signed-cut theorem gives W(n)<=C(n), so the signed-weight upper bound proves P(n)<=2C(n) for every positive n. For sharpness take n=2: its word is [false,true], a single antipalindrome but not a palindrome. The signed lower bound and this one-piece factorization give C(2)=1; the ordinary upper bound and impossibility of zero or one palindrome pieces give P(2)=2. Thus the equality is positive. All native minimum evidence at n=2 lives inside this theorem's existential proof branch. No unbounded sharpness family or assertion about shifted factors is needed. The separate Table 2 unbounded equal-cost assertion has different quantifiers."))), DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ambroz-kadlec-masakova-pelantova-2019-thue-morse-sharp-factor-two-prefix"),
                ResolutionKind.Proved)))));

    private static Formula V(string x) => F.Id(x);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Exists(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pl(Formula n) => Call("PL", Call("factor", n, D(0)));
    private static Formula Cost(Formula n) => Call("combinedLength", Call("factor", n, D(0)));

    private static Formula SharpFormula()
    {
        var n = V("n");
        var upper = All("n", N(), Imp(Le(D(1), n), Le(Pl(n), Mul(D(2), Cost(n)))));
        var attainer = Exists("n", N(), And(Le(D(1), n),
            And(Eqn(Pl(n), Mul(D(2), Cost(n))), LtF(D(0), Pl(n)))));
        return Disp(And(upper, attainer));
    }
}
