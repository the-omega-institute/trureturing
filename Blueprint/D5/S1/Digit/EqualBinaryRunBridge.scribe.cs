using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class EqualBinaryRunBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/EqualBinaryRunBridge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/oeis2025a386705");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal maximal binary run pairs have unique positive-part encodings, and their distinct integer sums satisfy the A386705 recurrence.",
        H("Equal Binary Run Pairs"),
        Blocks(
            Paragraph(Text("The source is the full OEIS A386705 record at "
                + "https://raw.githubusercontent.com/oeis/oeisdata/30c383550c8059b1712df8e32827d3b203765933/seq/A386/A386705.seq. "
                + "Its NAME is: a(n) = sum of the 2^(n-1) even positive integers having bit length 2*n "
                + "and in which, when written in binary, each run of 0's is of exactly the same length "
                + "as the run of 1's immediately before it. Its FORMULA is: Empirical: "
                + "a(n) = 12*a(n-1) - 36*a(n-2) + 32*a(n-3), with a(1) = 2, a(2) = 22, a(3) = 192. "
                + "The A166751 comment already associates zero runs with compositions. "
                + "The construction below does not claim that observation as new.")),
            Paragraph(Text("All indices and represented positive integers are natural numbers. "
                + "bits(m) reverses Nat.digits 2 m, giving the canonical most significant digit first word. "
                + "splitBy with Boolean equality forms the actual maximal constant runs. "
                + "Matched([]) is true; Matched([r]) is false; Matched(o::z::rest) requires every entry "
                + "of o to be one, every entry of z to be zero, equal lengths, and Matched(rest). "
                + "Every run returned by splitBy is nonempty. On a positive even canonical binary word, "
                + "this says exactly that each maximal zero run matches the preceding maximal one run.")),
            Paragraph(Text("Literal(n,m) requires m positive and even, bits(m) of length exactly 2*n, "
                + "and Matched of its maximal runs. row(n) filters the finite set of naturals below "
                + "2^(2*n) by Literal(n,m). The digit bound is proved in mem_row_iff, so this bound "
                + "omits no literal member. a(n) sums the distinct members of row(n), casting each "
                + "member to the integers. All arithmetic in the target recurrence is integer arithmetic; "
                + "natural subtraction is used only in indices under n>=4.")),
            Paragraph(Text("blockRuns([]) is empty. blockRuns(k::ks) consists of k ones, then k zeros, "
                + "then blockRuns(ks). word(ks) flattens this list of runs. Positive(ks) below means "
                + "every member is strictly positive. The proved maximal-run identity uses Mathlib's "
                + "splitBy_flatten and its chain conditions, including the zero-to-one boundaries "
                + "between successive pairs. Reconstruction uses the literal Matched predicate; "
                + "equal encoded words have equal maximal runs and hence equal part lists.")),
            Paragraph(Text("Decoding word(ks) with Nat.ofDigits recovers exactly its canonical bits "
                + "when all parts are positive. A nonempty such word starts in one and ends in zero, "
                + "so its decoded integer is positive and even. The finite set parts(n) is the image "
                + "of Mathlib's Composition(n) under its blocks projection. Its members are precisely "
                + "the positive lists summing to n; composition_card supplies its cardinality. "
                + "The all-ones digit identity is reused directly from ones_value in "
                + "D5.S1.Words.DoubleTailShuffleSupport, whose statement and proof are preserved. "
                + "For n>0, row(n) is the image of parts(n) under decoding, and decoding is injective "
                + "on that set. Consequently a(n) equals the integer sum of decoded composition words "
                + "with no repeated integer counted twice.")),
            Paragraph(Text("For n>=1, write W(n) for the sum of decoded words over parts(n), "
                + "T(n) for the sum of decoded tails, E(n) for the sum of 2^k*4^r, where k is "
                + "the first part and r is the sum of the remaining parts, and U(n)=4^n*2^(n-1). "
                + "Every composition of n+1 is uniquely either 1::ks or grow(ks), for a composition "
                + "ks of n; grow increments the first part. These two images are disjoint. "
                + "The decoded value of k::ks is (4^k-2^k)*4^sum(ks)+value(ks), in the integers. "
                + "Summing over the two images gives W(n+1)=5W(n)+2U(n)+2E(n)-3T(n), "
                + "T(n+1)=W(n)+T(n), E(n+1)=2U(n)+2E(n), and U(n+1)=8U(n). "
                + "The initial data W(1)=2, T(1)=0, E(1)=2 yield the invariant W(n)-T(n)+E(n)=U(n). "
                + "Thus W(n+1)=2W(n)-E(n)+5U(n); eliminating E and U proves "
                + "W(n+3)=12W(n+2)-36W(n+1)+32W(n). "
                + "The same identities give W(2)=22 and W(3)=192. The injective sum transport "
                + "identifies W(n) with the literal a(n), rather than defining a(n) by these equations.")),
            Describe.Lean(DescribeId.Create("equal-binary-run-membership"),
                DeclarationHandle.Create(Prefix + "mem_row_iff"), H("Unique literal encoding"),
                StatementSource.FromAuthor(MembershipFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This is a membership characterization for the actual set of integers. "
                    + "It proves existence and uniqueness of positive part lengths; it assumes neither "
                    + "a composition count nor an identity for the sum over those lengths. "
                    + "Positivity and evenness of the represented integer remain explicit on both sides."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-binary-run-full-target"),
                DeclarationHandle.Create(Prefix + "FullClaim"), H("Complete recurrence target"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("FullClaim names the complete conjunction. The theorem full_claim "
                    + "below proves it without assuming a recurrence, a composition count, or a weighted "
                    + "sum identity. The composition count is supplied by Mathlib and the weighted "
                    + "identities are derived from the finite composition split."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("equal-binary-run-full-claim"),
                DeclarationHandle.Create(Prefix + "full_claim"), H("Complete literal recurrence"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The three initial values and the recurrence hold for the actual "
                    + "distinct positive even integers with canonical bit length 2*n and equally paired "
                    + "maximal runs. Natural indices express every integer index n>=1 exactly; the "
                    + "recurrence guard n>=4 makes each shifted index positive. Every subtraction of "
                    + "sequence values is in the integers. This is a universal theorem, not finite-prefix "
                    + "verification. The source's empirical formula and the known composition relation "
                    + "are distinguished from the kernel-checked derivation."))), DescribeRole.Theorem))));

    private static Formula N() => F.Id("Nat");
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iffn(Formula x, Formula y) => Seq(x, Sp, Iff, Sp, y);
    private static Formula Bin(Formula x, FormulaBinaryOperator op, Formula y) => new Formula.Binary(x, op, y);
    private static Formula Pred(Formula n, byte k) => Bin(n, FormulaBinaryOperator.Subtract, D(k));
    private static Formula MembershipFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var p = F.Id("p"); var q = F.Id("q");
        Formula Lists() => Call("List", N());
        Formula Encoding(Formula v) => And(Call("Positive", v),
            And(Eqn(Call("sum", v), n), Eqn(Call("bits", m), Call("word", v))));
        var unique = Ex("p", Lists(), And(Encoding(p), All("q", Lists(), Imp(Encoding(q), Eqn(q, p)))));
        return Disp(All("n", N(), All("m", N(), Iffn(
            new Formula.Relation(m, FormulaRelationOperator.MemberOf, Call("row", n)),
            And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m), And(Call("Even", m), unique))))));
    }
    private static Formula ClaimFormula() => Disp(Iffn(F.Id("FullClaim"), ClaimBody()));
    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var rhs = Bin(Bin(D(1, 2), FormulaBinaryOperator.Multiply, Call("a", Pred(n, 1))),
            FormulaBinaryOperator.Subtract, Bin(D(3, 6), FormulaBinaryOperator.Multiply, Call("a", Pred(n, 2))));
        rhs = Bin(rhs, FormulaBinaryOperator.Add, Bin(D(3, 2), FormulaBinaryOperator.Multiply, Call("a", Pred(n, 3))));
        var recurrence = All("n", N(), Imp(new Formula.Relation(D(4), FormulaRelationOperator.LessThanOrEqual, n),
            Eqn(Call("a", n), rhs)));
        return And(Eqn(Call("a", D(1)), D(2)),
            And(Eqn(Call("a", D(2)), D(2, 2)), And(Eqn(Call("a", D(3)), D(1, 9, 2)), recurrence)));
    }
}
