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
                + "D5.S1.Words.DoubleTailShuffleSupport. "
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
            Definition("bits", "Canonical binary digits", BitsFormula(),
                "The result is a list of natural-number digits in most significant digit first order. "
                + "The definition includes m=0, whose digit list is empty."),
            Definition("Matched", "Matching successive run pairs", MatchedFormula(),
                "These three equations cover every list of runs. The singleton case is false. "
                + "The paired case does not itself require nonempty runs: empty runs are allowed here. "
                + "Nonemptiness in Literal comes from splitting the canonical word into maximal runs."),
            Definition("Literal", "Literal source membership", LiteralFormula(),
                "The Boolean comparator BEq.beq tests equality of natural-number digits. "
                + "List.splitBy retains the word order and groups adjacent equal digits. "
                + "Both n and m range over all naturals, including zero; positivity is an explicit conjunct."),
            Definition("row", "Finite set of literal integers", RowFormula(),
                "The result has type Finset Nat. Finset.range excludes its upper bound, and "
                + "Finset.filter keeps exactly those members satisfying Literal. This includes row zero."),
            Definition("a", "Distinct integer sum", SumFormula(),
                "The sum is indexed by the finite set row(n), so each natural-number member occurs once. "
                + "Each summand is explicitly cast to the integers; an empty row has sum zero."),
            Definition("blockRuns", "Ordered one-zero block pairs", BlockRunsFormula(),
                "List.cons prepends one whole run. Each part contributes its run of ones before its "
                + "run of zeros. The equations apply to every natural k, including k=0, which contributes "
                + "two empty runs; no positivity hypothesis is imposed by this definition."),
            Definition("word", "Concatenated block word", WordFormula(),
                "The input is any list of natural part lengths. List.flatten concatenates its runs "
                + "in order, including empty runs; the empty input gives the empty word."),
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
                    + "are distinguished from the kernel-checked derivation."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a386705-equal-binary-run-sum-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string commentary) =>
        Describe.Lean(DescribeId.Create("equal-binary-run-definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(commentary))), DescribeRole.Definition);

    private static Formula N() => F.Id("Nat");
    private static Formula Lists() => Call("List", N());
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula Cons(Formula head, Formula tail) => Qualified("List", "cons", head, tail);
    private static Formula Typed(Formula term, Formula type) => Seq(Open, term, Colon, Sp, type, Close);
    private static Formula BitsFormula()
    {
        var m = F.Id("m");
        return Disp(All("m", N(), Eqn(Call("bits", m),
            Qualified("List", "reverse", Qualified("Nat", "digits", D(2), m)))));
    }
    private static Formula MatchedFormula()
    {
        var r = F.Id("r"); var o = F.Id("o"); var z = F.Id("z"); var rest = F.Id("rest");
        var d = F.Id("d");
        Formula Entries(Formula run, Formula digit) => All("d", N(), Imp(
            new Formula.Relation(d, FormulaRelationOperator.MemberOf, run), Eqn(d, digit)));
        return Disp(new Formula.Aligned([
            Iffn(Call("Matched", EmptyList()), F.Id("True")),
            All("r", Lists(), Iffn(Call("Matched", Cons(r, EmptyList())), F.Id("False"))),
            All("o", Lists(), All("z", Lists(), All("rest", Call("List", Lists()),
                Iffn(Call("Matched", Cons(o, Cons(z, rest))),
                    And(Entries(o, D(1)), And(Entries(z, D(0)),
                        And(Eqn(Qualified("List", "length", o), Qualified("List", "length", z)),
                            Call("Matched", rest))))))))
        ]));
    }
    private static Formula LiteralFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var x = F.Id("x"); var y = F.Id("y");
        var comparator = Seq(LambdaLower, Sp, Typed(x, N()), Sp, Typed(y, N()), Sp, Mapsto, Sp,
            Typed(Qualified("BEq", "beq", x, y), F.Id("Bool")));
        return Disp(All("n", N(), All("m", N(), Iffn(Call("Literal", n, m),
            And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m),
                And(Call("Even", m), And(
                    Eqn(Qualified("List", "length", Call("bits", m)),
                        Bin(D(2), FormulaBinaryOperator.Multiply, n)),
                    Call("Matched", Qualified("List", "splitBy", comparator, Call("bits", m))))))))));
    }
    private static Formula RowFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", N(), Eqn(Call("row", n), Qualified("Finset", "filter",
            Call("Literal", n), Qualified("Finset", "range",
                new Formula.Power(D(2), Bin(D(2), FormulaBinaryOperator.Multiply, n)))))));
    }
    private static Formula SumFormula()
    {
        var n = F.Id("n"); var m = F.Id("m");
        return Disp(All("n", N(), Eqn(Call("a", n),
            Seq(Sum, Underscore, Grp(Typed(m, N()), Sp, InMacro, Sp, Call("row", n)), Sp,
                Typed(m, Seq(Mathbb, Grp(F.Id("Z"))))))));
    }
    private static Formula BlockRunsFormula()
    {
        var k = F.Id("k"); var ks = F.Id("ks");
        return Disp(new Formula.Aligned([
            Eqn(Call("blockRuns", EmptyList()), EmptyList()),
            All("k", N(), All("ks", Lists(), Eqn(Call("blockRuns", Cons(k, ks)),
                Cons(Qualified("List", "replicate", k, D(1)),
                    Cons(Qualified("List", "replicate", k, D(0)), Call("blockRuns", ks))))))
        ]));
    }
    private static Formula WordFormula()
    {
        var ks = F.Id("ks");
        return Disp(All("ks", Lists(), Eqn(Call("word", ks),
            Qualified("List", "flatten", Call("blockRuns", ks)))));
    }
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
