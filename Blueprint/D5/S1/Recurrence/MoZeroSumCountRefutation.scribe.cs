using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MoZeroSumCountRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MoZeroSumCountRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/johnc2026mo516232r2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An alternating positive integer sequence has C-finite zero-sum counts for every "
            + "finite integer digit set while its expanding characteristic roots have "
            + "a ratio which is not a root of unity.",
        H("A Counterexample to the Zero-Sum Count Characterization"),
        Blocks(
            Paragraph(Text(
                "John C's MathOverflow question 516232, revision 2, proposes a characterization "
                    + "of constant-coefficient recurrences for exact zero-sum prefix counts. "
                    + "The statement concerns every positive integer recurrence sequence and every "
                    + "finite integer digit set. The counterexample below refutes that entire iff. "
                    + "Historical priority and complete earlier coverage remain UNKNOWN: the "
                    + "original full Frougny 1992 article has not been obtained. Standard bounded "
                    + "binary carries and finite automata are not claimed as new methods.")),
            Node("sequence", "The alternating sequence", SequenceFormula(),
                "Lean index zero is source index one. Thus the source sequence has "
                    + "a(2k-1)=4^k and a(2k)=2^k for k at least one; its first terms "
                    + "are 4,2,16,4,64,8. Every term is positive. For every original "
                    + "index it satisfies a(n+4)=6a(n+2)-8a(n). The decreases at some "
                    + "indices are permitted by the source.", DescribeRole.Definition),
            Node("characteristic", "The minimal characteristic polynomial",
                Disp(Eq(F.Id("P"), Mul(Sub(Pow(F.Id("X"), D(2)), D(4)),
                    Sub(Pow(F.Id("X"), D(2)), D(2))))),
                "The monic polynomial is X^4-6X^2+8. An annihilator of degree below four "
                    + "would give four linear equations from the first four shifts of the "
                    + "sequence. Their values 4,2,16,4,64,8,256 force all four possible "
                    + "coefficients to vanish. Hence no monic integer annihilator of smaller "
                    + "degree exists.", DescribeRole.Definition),
            Node("Annihilates", "Annihilation in the forward shift", null,
                "Annihilates(a,p) means that, for every natural n, the sum of p's coefficient "
                    + "at j times a(n+j), over p's support, is zero. Integer coefficients and "
                    + "the original sequence indices are retained.", DescribeRole.Definition),
            Node("MinimalCharacteristic", "The actual minimal integer recurrence", null,
                "MinimalCharacteristic(a,p) requires p to be monic, to annihilate a at "
                    + "every index, and to have degree at most that of every other monic "
                    + "integer annihilator. These clauses include the original constant "
                    + "integer recurrence hypothesis; they do not postulate a candidate "
                    + "polynomial without proving its minimality.", DescribeRole.Definition),
            Node("zeroAssignments", "Ordered original-coordinate assignments", null,
                "An assignment is a function from Fin(n) to the given finite integer "
                    + "set D whose sum of digit times the original sequence weight is zero. "
                    + "Two different original coordinates remain distinct even when their "
                    + "weights coincide. No set of possible digit sums replaces the "
                    + "ordered assignments.", DescribeRole.Definition),
            Node("sourceCount", "Exact prefix counts", null,
                "sourceCount(a,D,n) is the cardinality of zeroAssignments(a,D,n). "
                    + "For positive n this is exactly the source count. Length zero has "
                    + "one empty assignment; its value is used only to simplify the finite "
                    + "state evolution and is removed by the explicit length-one shift "
                    + "in CountRecurrence.", DescribeRole.Definition),
            Node("CountRecurrence", "The source recurrence convention", null,
                "CountRecurrence(s) allows any positive order k, any complex coefficient "
                    + "vector, and any initial cutoff N; at every n at least N it asserts "
                    + "s(n+k+1)=sum c(i)s(n+i+1). Thus it imposes neither a coefficient "
                    + "restriction nor a common order for different digit sets. The proof "
                    + "constructs integer coefficients valid from length zero, casts them "
                    + "to the complex numbers, and applies the recurrence at n+1.",
                DescribeRole.Definition),
            Node("RootConditions", "All three complex-root clauses", RootFormula(),
                "The roots are complex roots of the integer polynomial after coefficient "
                    + "casting. The first clause excludes norm one. The second requires "
                    + "multiplicity one at every root of norm greater than one. The third "
                    + "quantifies over every pair of such roots and requires a positive "
                    + "integer power of their ratio to equal one.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mo516232-whole-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The entire displayed iff"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The quantifiers include every integer-valued sequence with positive "
                        + "terms, its actual minimal characteristic polynomial, and every "
                        + "finite integer digit set. There is no increasing-sequence "
                        + "assumption, bounded alphabet, bounded order, selected prefix, "
                        + "or omitted root clause."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mo516232-whole-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("The characterization is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix any finite integer D, including the empty set, and let M be "
                            + "the supremum of its digits' absolute values, with empty supremum zero. "
                            + "Carries range from -2M through 2M. The matrix T(m) counts "
                            + "ordered m-tuples of digits satisfying c+sum(d)=2c'. "
                            + "Only m=0,1,2 occurs. A zero assignment splits uniquely into "
                            + "its first local tuple and its suffix, with next carry equal "
                            + "to minus the suffix's binary value. The local digit bound "
                            + "proves that this integer carry remains in the stated interval. "
                            + "This bijection proves exact counting by matrix multiplication, "
                            + "with both endpoint carries zero.")),
                    Paragraph(Text(
                        "At Lean coordinate i, the binary exponent after division of all "
                            + "weights by two is i+1 for even i and floor(i/2) for odd i. "
                            + "Each exponent fiber has at most two coordinates. Reindexing "
                            + "the original assignments by these fibers is a bijection and "
                            + "preserves their weighted sum. At exponent j its cardinality "
                            + "is the sum of the indicator that j is odd and the indicator "
                            + "that j is below floor(n/2). Missing exponents have cardinality "
                            + "zero and retain their T(0) factor.")),
                    Paragraph(Text(
                        "Increasing the prefix length by four prepends multiplicities "
                            + "(1,2) and appends (0,1). Therefore the entire product Q(n) "
                            + "satisfies Q(n+4)=A Q(n) B, where A=T(1)T(2) and "
                            + "B=T(0)T(1). This identity holds for all n, including zero, "
                            + "and covers all four residue classes. Column vectorization "
                            + "turns it into v(n+4)=(transpose(B) tensor A)v(n), using "
                            + "mathlib's exact Kronecker identity.")),
                    Paragraph(Text(
                        "The state consisting of v(n),v(n+1),v(n+2),v(n+3) advances "
                            + "by one fixed integer matrix W. Cayley-Hamilton gives a "
                            + "monic integer recurrence for every coordinate, including "
                            + "the zero-carry entry equal to the exact original count. "
                            + "Its positive order is the cardinality of the four-phase "
                            + "state space. The construction is uniform in D and proves "
                            + "the required recurrence at every source index.")),
                    Paragraph(Text(
                        "The actual minimal polynomial has roots 2 and sqrt(2). "
                            + "Both have norm greater than one, and their ratio has norm "
                            + "greater than one. Its positive powers cannot equal one. "
                            + "Thus the universal-D count property holds for this sequence "
                            + "while the asserted conjunction of root conditions fails. "
                            + "This contradicts the only-if implication and refutes the "
                            + "entire iff. No replacement classification or historical "
                            + "originality claim is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mo516232-zero-sum-count-characterization"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula? formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mo516232-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula SequenceFormula()
    {
        var k = F.Id("k");
        return Disp(All("k", Numbers("N"), And(
            Eq(Call("a", Mul(D(2), k)), Pow(D(4), Add(k, D(1)))),
            Eq(Call("a", Add(Mul(D(2), k), D(1))), Pow(D(2), Add(k, D(1)))))));
    }

    private static Formula RootFormula()
    {
        var p = F.Id("P");
        var z = F.Id("z");
        var w = F.Id("w");
        var k = F.Id("k");
        var first = All("z", Numbers("C"), Imply(Call("Root", p, z),
            new Formula.Not(Eq(Call("norm", z), D(1)))));
        var second = All("z", Numbers("C"), Imply(Call("Root", p, z),
            Imply(Lt(D(1), Call("norm", z)), Eq(Call("rootMultiplicity", p, z), D(1)))));
        var third = All("z", Numbers("C"), All("w", Numbers("C"),
            Imply(Call("Root", p, z), Imply(Call("Root", p, w),
                Imply(Lt(D(1), Call("norm", z)), Imply(Lt(D(1), Call("norm", w)),
                    Exists("k", Numbers("N"), And(Lt(D(0), k),
                        Eq(Pow(new Formula.Fraction(z, w), k), D(1))))))))));
        return Disp(All("P", Call("IntegerPolynomials"),
            Iff(Call("RootConditions", p), And(first, And(second, third)))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var p = F.Id("P");
        return Disp(Iff(F.Id("claim"), All("a", Call("IntegerSequences"),
            All("P", Call("IntegerPolynomials"),
                Imply(All("n", Numbers("N"), Lt(D(0), Call("a", F.Id("n")))),
                    Imply(Call("MinimalCharacteristic", a, p),
                        Iff(All("D", Call("FiniteIntegerSets"),
                            Call("CountRecurrence", Call("sourceCount", a, F.Id("D")))),
                            Call("RootConditions", p))))))));
    }

    private static Formula Numbers(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.BindMany(q, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Imply(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
