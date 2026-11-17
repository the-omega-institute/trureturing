using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class OnnGoodPermutationCountDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/onn2023supmodular");
    private const string Question = "Section 2, page 4, immediately before Lemma 2.2: “An interesting question suggested by a referee is to count and characterize, for every m and n, those permutations which are good for all 1≤i<m and 1≤j<n.” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact good-permutation counts in every positive dimension.", H("Counting good permutations"),
        Blocks(
            Paragraph(Text("Arrays are equivalences (Fin m × Fin n) ≃ Fin (m*n), and entry adds one to each rank. "
                + "Good and Structure are the predicates of OnnGoodPermutationStructure. Nat.card counts the finite subtype of equivalences. "
                + "All subtractions and powers below are natural-number operations.")),
            Node("goodCount", "The number of good rank arrays", AllN("m", AllN("n",
                Equal(Call("goodCount", V("m"), V("n")), App(Q("Nat", "card"), Subtype("s", Array(), Call("Good", V("s"))))))),
                Question + "Each equivalence supplies exactly one placement of the labels 1,…,mn.", true, true),
            Node("proposedCount", "The four counting cases", CountFormula(),
                "The smaller dimension selects the factorial and power-of-two cases. The remaining positive cases give 72 for three by three and zero otherwise.", true),
            Node("claim", "The referee's counting and characterization question", Equal(V("claim"), Parenthesized(ClaimBody())),
                Question + "The quantifiers range over all positive natural dimensions and every rank array in either orientation. "
                + "The two-row split is unique, including its endpoint cases; the three-by-three alternatives are the two ordered-list types.", true, true),
            Node("result", "The count and characterization in all dimensions", ClaimBody(),
                "A unique sign transition splits a good two-row array into two disjoint chains. Their label sets run through all even subsets of Fin (2*n), giving 2^(2*n−1). "
                + "The two three-by-three types have center label 5 and two independent interleavings of two ordered pairs, hence 36 each. "
                + "One-dimensional arrays contribute every permutation; overlapping three-by-three blocks exclude the remaining dimensions.",
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-onn2023good"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("onn-count-" + name.ToLowerInvariant()), DeclarationHandle.Create(Root + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem,
        openProblemResolutionClaim: resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula AllN(string name, Formula body) => All(name, Nat, body);
    private static Formula Array() => Parenthesized(Seq(Parenthesized(Seq(Call("Fin", V("m")), Times, Call("Fin", V("n")))), Equiv,
        Call("Fin", Mul(V("m"), V("n")))));
    private static Formula Subtype(string name, Formula type, Formula condition) => Seq(OpenBrace, V(name), Colon, type, Bar, condition, CloseBrace);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula If(Formula c, Formula t, Formula f) => Seq(V("if"), Sp, Parenthesized(c), Sp, V("then"), Sp, t, Sp, V("else"), Sp, Parenthesized(f));
    private static Formula CountFormula()
    {
        var min = Call("min", V("m"), V("n")); var max = Call("max", V("m"), V("n"));
        var body = If(Equal(min, D(1)), App(Q("Nat", "factorial"), max),
            If(Equal(min, D(2)), new Formula.Power(D(2), Sub(Mul(D(2), max), D(1))),
                If(AndF(Equal(V("m"), D(3)), Equal(V("n"), D(3))), D(7, 2), D(0))));
        return AllN("m", AllN("n", Equal(Call("proposedCount", V("m"), V("n")), body)));
    }
    private static Formula ClaimBody() => AllN("m", AllN("n", Imp(LtF(D(0), V("m")), Imp(LtF(D(0), V("n")),
        AndF(Equal(Call("goodCount", V("m"), V("n")), Call("proposedCount", V("m"), V("n"))),
            All("s", Array(), IffF(Call("Good", V("s")), Call("Structure", V("s")))))))));
}
