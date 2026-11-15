using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class MurthyA087371ExponentRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/murthy2003a087371");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least positive prime-producing exponents in OEIS A087371 are unbounded.",
        H("Murthy's decimal bounded exponent conjecture is false"),
        Blocks(
            Node("a", "The least positive exponent", SequenceFormula(),
                "OEIS A087371, NAME (unpaginated), defines the least exponent for which "
                + "10^k+2n-1 is a prime strictly greater than ten, or zero if none exists. "
                + "The displayed set retains all three conditions: k is positive, the candidate "
                + "is prime, and its value exceeds ten. Exponent zero cannot qualify: for n at "
                + "least one its candidate is 2n, and an even prime is two, which fails the "
                + "strict threshold. Thus the positive-exponent convention agrees with the "
                + "source even if its smallest-power wording is read as allowing exponent zero. "
                + "Nat.find takes the least member of the nonempty set, testing every earlier "
                + "positive exponent; the empty-set branch is exactly zero. The definition is "
                + "total on natural n, and the conjecture uses the source's offset-one domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The full boundedness assertion",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A087371, COMMENTS (unpaginated): "
                + "\"Conjecture: There exists a finite M such that a(n) < M for all n.\" "
                + "Both M and n range over natural numbers, with n at least one. The same M "
                + "must work for every such n, and the inequality is strict.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "No finite bound exists", Disp(new Formula.Not(F.Id("claim"))),
                "Fix any positive K. Apply PrimeGap.exists_primeGap_ge to 10^K, obtaining "
                + "consecutive primes q<p with p-q at least 10^K. Since q is at least two, "
                + "p is strictly greater than ten. The upper prime p is odd, whereas 10^K "
                + "is even. Hence p-10^K is a positive odd integer. Write p-10^K=2m+1 "
                + "and set n=m+1, so n is at least one and 10^K+2n-1=p. This is a "
                + "qualifying prime strictly greater than ten at exponent K. For every natural "
                + "j<K, including zero, the candidate 10^j+2n-1 lies strictly between q and p, "
                + "hence is composite by Nat.nth_add_one_le_iff. In particular every earlier "
                + "positive exponent fails. Thus the qualifying set is nonempty and its least "
                + "member is exactly K: a(n)=K. Given a proposed bound M, take K=M+1 to "
                + "contradict a(n)<M. This supplies genuine first successes of every positive "
                + "size without a cutoff, while retaining the zero value whenever no exponent "
                + "qualifies. The consecutive-prime-gap theorem is reused directly; the offset, "
                + "threshold and leastness are checked for this decimal sequence. No theorem "
                + "about the separate base-three sequence is assumed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("murthy-a087371-bounded-exponent"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("murthy-a087371-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula ExistsNat(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Candidate(Formula k, Formula n) =>
        Subtract(Add(new Formula.Power(D(1, 0), k), Multiply(D(2), n)), D(1));
    private static Formula Qualifies(Formula k, Formula n) => new Formula.Logic(
        Le(D(1), k), FormulaLogicOperator.And,
        new Formula.Logic(Call("Prime", Candidate(k, n)), FormulaLogicOperator.And,
            Lt(D(1, 0), Candidate(k, n))));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var set = Seq(OpenBrace, k, Sp, Colon, Sp, Nat, Sp, Mid, Sp,
            Qualifies(k, n), CloseBrace);
        var cases = Seq(Begin, Grp(F.Id("cases")), Call("min", set), Amp,
            ExistsNat("k", Qualifies(k, n)), RowBreak, D(0), Amp,
            new Formula.Not(Parenthesized(ExistsNat("k", Qualifies(k, n)))),
            End, Grp(F.Id("cases")));
        return Disp(All("n", Equal(Call("a", n), cases)));
    }

    private static Formula ClaimBody() => ExistsNat("M", All("n",
        Imp(Le(D(1), F.Id("n")), Lt(Call("a", F.Id("n")), F.Id("M")))));
}
