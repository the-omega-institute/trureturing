using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class IanakievShortestRulerPalindromeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ianakiev2019a094373");
    private static readonly LibraryNoteRef Plateaus =
        LibraryNoteRef.Create("D5/L/Factorization/kullmannzhao2015smarandache");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal factorial run lengths have exactly the shortest-palindrome first occurrences specified by Ianakiev.",
        H("Ianakiev's shortest palindromes of factorial run lengths"),
        Blocks(
            Paragraph(Text("All indices and lengths are natural numbers. F has offset zero and is the least positive factorial index. The constant runs include its initial singleton. B and the source's third sequence P use positive indices. The first value P(1)=1 is stipulated; the minimum over palindrome lengths at least two applies only at indices at least two. A has offset zero. Every palindrome is a contiguous block.")),
            Node("F", "Least positive factorial indices", FactorialMinimum(),
                "For every exponent m, F(m) is the least positive h with 2^m dividing h!. Such an h exists because 2^m divides its own factorial. In particular F(0)=1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("S", "Successive maximal constant runs", BoundaryMinimum(),
                "S(0)=0. Each following boundary is the least strictly later exponent where F changes. Minimality makes F constant throughout the intervening run, and membership makes the next run start with a different value. Every such boundary exists.",
                AssessedProvenance.FromLiterature(Source)),
            Node("B", "Lengths of the actual runs",
                All("i", Eqn(Call("B", V("i")), Sub(Call("S", V("i")), Call("S", Sub(V("i"), D(1)))))),
                "At positive i, B(i)=S(i)-S(i-1). The initial value is B(1)=1. For r positive, B(r+1)=1+v2(r). This follows from the actual factorial minima and boundaries: S(r+1)=v2((2r)!)+1 and F(S(r+1))=2(r+1). The positive plateau identification is classical; the initial singleton retains the least-positive convention.",
                AssessedProvenance.FromLiterature(Plateaus)),
            Node("Pal", "Contiguous reflection",
                All("i", All("L", Iffn(Call("Pal", V("i"), V("L")),
                    All("t", Implies(Lt(V("t"), V("L")),
                        Eqn(Call("B", Add(V("i"), V("t"))),
                            Call("B", Sub(Sub(Add(V("i"), V("L")), D(1)), V("t"))))))))),
                "The indices paired by reflection are i+t and i+L-1-t for every t<L. Length at least two is a separate admissibility condition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("P", "The shortest admissible length",
                And(Eqn(Call("P", D(1)), D(1)), PalindromeMinimum()),
                "The admissible-length set is nonempty at every i at least two. P(i) is its least member, rather than a definition by a proposed closed formula. Index zero is outside the source's third sequence.",
                AssessedProvenance.FromLiterature(Source)),
            Node("A", "The present OEIS sequence",
                And(Eqn(Call("A", D(0)), D(1)),
                    All("e", Eqn(Call("A", Add(V("e"), D(1))), Add(Pow(D(2), V("e")), D(1))))),
                "The formula preceding Ianakiev's comment gives A(0)=1 and A(e+1)=2^e+1. The sequence A is strictly increasing.",
                AssessedProvenance.FromLiterature(Source)),
            Node("First", "First appearances",
                All("i", Iffn(Call("First", V("i")),
                    All("j", Implies(And(Le(D(1), V("j")), Lt(V("j"), V("i"))),
                        Neqn(Call("P", V("j")), Call("P", V("i"))))))),
                "A value first appears at i precisely when every earlier positive position has a different value.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete two-clause assertion", Iffn(V("claim"), CompleteStatement()),
                "The assertion includes existence and minimality of every factorial index, every successive boundary, and every admissible palindrome minimum. Its two conclusions give the entire increasing first-occurrence list and the value at every specified A-position. Neither conclusion is restricted to a finite prefix.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "All minima and both conclusions", CompleteStatement(),
                "Write j=i-1, k=v2(j), and q=2^k for i at least two. Equal endpoint values in a palindrome force its endpoint indices to have equal valuations. Their odd quotients differ by at least two, so every admissible length is at least 2q+1. The center c=j+q is divisible by 2^(k+1). For each positive s at most q, v2(s) is at most k, and the unequal-valuation addition law gives v2(c-s)=v2(c+s). This supplies the full palindrome of length 2q+1, proving P(i)=2^(v2(i-1)+1)+1. The least positive integer of valuation k is 2^k. Thus each later value first occurs at 2^k+1, while P(1)=1 is the initial first occurrence. At m at least two, substituting i=A(m-1) gives P(i)=A(m). The argument is specific to the binary factorial runs; no arbitrary-prime analogue is asserted.",
                AssessedProvenance.FromRepo(Source, Plateaus), true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a094373-ianakiev-shortest-ruler-palindrome"),
                    ResolutionKind.Proved)))));

    private static Formula FactorialMinimum()
    {
        Formula m = V("m"), h = V("h"), value = Call("F", m);
        return All("m", And(Le(D(1), value), Dvd(Pow(D(2), m), Fact(value)),
            All("h", Implies(And(Le(D(1), h), Dvd(Pow(D(2), m), Fact(h))), Le(value, h)))));
    }

    private static Formula BoundaryMinimum()
    {
        Formula r = V("r"), m = V("m"), start = Call("S", r), next = Call("S", Add(r, D(1)));
        Formula Changes(Formula at) => And(Lt(start, at), Neqn(Call("F", at), Call("F", start)));
        return And(Eqn(Call("S", D(0)), D(0)),
            All("r", And(Changes(next), All("m", Implies(Changes(m), Le(next, m))))));
    }

    private static Formula PalindromeMinimum()
    {
        Formula i = V("i"), length = V("L"), value = Call("P", i);
        Formula Legal(Formula at) => And(Le(D(2), at), Call("Pal", i, at));
        return All("i", Implies(Le(D(2), i),
            And(Legal(value), All("L", Implies(Legal(length), Le(value, length))))));
    }

    private static Formula CompleteStatement()
    {
        Formula i = V("i"), m = V("m");
        return And(FactorialMinimum(), BoundaryMinimum(), Eqn(Call("P", D(1)), D(1)),
            PalindromeMinimum(), Call("StrictMono", V("A")),
            All("i", Implies(Le(D(1), i), Iffn(Call("First", i),
                Exists("m", Eqn(i, Call("A", m)))))),
            All("m", Implies(Le(D(2), m),
                Eqn(Call("P", Call("A", Sub(m, D(1)))), Call("A", m)))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, bool theorem = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ianakiev-shortest-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Fact(Formula a) => Seq(a, Bang);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Neqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string name, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,
        FormulaIdentifier.Create(name), new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula Exists(string name, Formula body) => new Formula.Bind(FormulaQuantifier.Exists,
        FormulaIdentifier.Create(name), new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = rest[^1];
        for (int i = rest.Length - 1; i >= 0; --i)
            result = new Formula.Logic(Par(i == 0 ? first : rest[i - 1]), FormulaLogicOperator.And, Par(result));
        return result;
    }
}
