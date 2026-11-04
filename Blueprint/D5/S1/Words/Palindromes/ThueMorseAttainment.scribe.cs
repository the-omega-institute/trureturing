using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class ThueMorseAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/ThueMorseAttainment.";
    private static readonly LibraryNoteRef Akmp = LibraryNoteRef.Create("D5/L/Words/ambrozetal2019palindromiclength");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit unbounded family of literal Thue-Morse prefixes has equal ordinary and mixed palindromic costs.",
        H("Attaining Thue-Morse Prefixes"), Blocks(
        Describe.Lean(DescribeId.Create("tm-attaining-length"), DeclarationHandle.Create(Prefix + "attainingLength"),
            H("The positive prefix family"), StatementSource.FromAuthor(Disp(And(
                Eqn(Call("attainingLength", D(0)), D(1)), All("m", N(),
                Eqn(Call("attainingLength", Add(V("m"), D(1))),
                    Call("natSub", Mul(D(4), Call("attainingLength", V("m"))), D(1))))))),
            AssessedProvenance.FromRepo(Akmp), Blocks(Paragraph(Text("Index zero denotes n_1=1. Every next positive length is four times its predecessor minus one. NatSub is truncated natural subtraction. The signed expansion is the least-significant-first list obtained from [1] by prepending [-1,0] at each step; the existing nonadjacent signed-digit minimality theorem gives its weight m+1."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("tm-family-attains"), DeclarationHandle.Create(Prefix + "family_attains"),
            H("Exact attainment on the same literal family"), StatementSource.FromAuthor(Disp(All("m", N(), And(
                Eqn(Call("signedWeight", Call("int", Len(V("m")))), Add(V("m"), D(1))),
                And(Eqn(Cost(Len(V("m"))), Add(V("m"), D(1))), Eqn(Pl(Len(V("m"))), Add(V("m"), D(1)))))))),
            AssessedProvenance.FromRepo(Akmp), Blocks(Paragraph(Text("The substitution tau sends b to [b,not b,not b,b]. Reversing a substituted word commutes with substitution, so images of nonempty palindrome factors remain nonempty palindromes. Applying it to every factor gives PL(tau(w)) <= PL(w). The original even/odd Thue-Morse recurrences identify tau(t[0:n)) with t[0:4n). The existing ordinary-PL one-letter Lipschitz theorem then gives PL(t[0:4n-1)) <= PL(t[0:n))+1. Induction gives the ordinary upper bound on this exact family. The universal literal-cut lower bound sandwiches the actual mixed minimum between signed weight m+1 and ordinary PL m+1. Transporting an actual factorization under the substitution supplies the ordinary upper bound."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("tm-unbounded-equal-cost"), DeclarationHandle.Create(Prefix + "unbounded_equal_cost"),
            H("The whole quantified Section 6 assertion"), StatementSource.FromAuthor(Disp(All("K", N(),
                Imp(Le(D(1), V("K")), Exists("n", N(), And(Le(D(1), V("n")),
                    And(Eqn(Cost(V("n")), Pl(V("n"))), Le(V("K"), Pl(V("n")))))))))),
            AssessedProvenance.FromRepo(Akmp), Blocks(Paragraph(Text("The final paragraph of Section 6 and Table 2 motivate this exact quantified assertion. Choose n=attainingLength(K); both minima equal K+1. The word is Complexity.factor(n,0), with false=a and true=b. Ordinary PL minimizes nonempty palindrome factors; combinedLength minimizes nonempty factors that are palindromes or exchange-reversal antipalindromes. No derivative cost, parity proxy, empty factor or restricted window replaces these definitions. The substitution and signed-cut arguments establish the motivating assertion."))), DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ambroz-kadlec-masakova-pelantova-2019-thue-morse-equal-cost"),
                ResolutionKind.Proved)))));

    private static Formula V(string x) => F.Id(x);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Exists(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Len(Formula m) => Call("attainingLength", m);
    private static Formula Word(Formula n) => Call("factor", n, D(0));
    private static Formula Cost(Formula n) => Call("combinedLength", Word(n));
    private static Formula Pl(Formula n) => Call("PL", Word(n));
}
