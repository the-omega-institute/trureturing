using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class MurthyA087372ExponentRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/murthy2003a087372");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least positive prime-producing exponents in OEIS A087372 are unbounded.",
        H("Murthy's bounded exponent conjecture is false"),
        Blocks(
            Node("a", "The least positive exponent", SequenceFormula(),
                "OEIS A087372, NAME (unpaginated), defines the least exponent producing a prime, "
                + "or zero if none exists. Exponents are positive natural numbers: EXAMPLE gives "
                + "a(23)=3, since 49 and 55 are composite and 73 is prime. Allowing exponent zero "
                + "would give 47 and contradict that example. Nat.find chooses the least member "
                + "of the displayed nonempty set, testing every earlier positive exponent; the "
                + "empty-set branch is exactly zero. The definition is total on natural n, "
                + "and the conjecture uses the source's offset-one domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The full boundedness assertion",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A087372, COMMENTS (unpaginated): "
                + "\"Conjecture: There exists a finite M such that a(n) < M for all n.\" "
                + "Both M and n range over natural numbers, with n at least one. The same M "
                + "must work for every such n, and the inequality is strict.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "No finite bound exists", Disp(new Formula.Not(F.Id("claim"))),
                "Fix any positive K. Apply PrimeGap.exists_primeGap_ge to 3^K, obtaining "
                + "consecutive primes q<p with p-q at least 3^K. The upper prime p is odd and "
                + "p-3^K is even and at least two. Write p-3^K=2n, so n is at least one. "
                + "At exponent K the candidate is p. For every positive j<K, the candidate "
                + "3^j+2n lies strictly between q and p, hence is composite. The absence of a "
                + "prime in this interval follows from Nat.nth_add_one_le_iff. Thus the "
                + "qualifying set is nonempty and its least member is exactly K: a(n)=K. "
                + "Given a proposed bound M, take K=M+1 to contradict a(n)<M. This constructs "
                + "actual first successes of every positive size; it imposes no cutoff and "
                + "does not infer a bound from only the successful inputs. The consecutive-prime "
                + "gap theorem is reused; the exponent construction is derived here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("murthy-a087372-bounded-exponent"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("murthy-a087372-" + name), DeclarationHandle.Create(Prefix + name),
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
    private static Formula Qualifies(Formula k, Formula n) => new Formula.Logic(
        Le(D(1), k), FormulaLogicOperator.And,
        Call("Prime", Add(new Formula.Power(D(3), k), Multiply(D(2), n))));

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
