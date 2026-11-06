using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class ProvvediEvenFubiniLeastPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/provvedi2020a249938");

    private const string SourceSentence =
        "This sequence is a periodic sequence modulo m, and if m is the k-th prime, "
        + "the periods of {a(n)} over k-th prime is the sequence of the number of "
        + "nonzero quadratic residues modulo k-th prime, for all k>0.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive even-index Fubini sequence has the conjectured least period at every prime.",
        H("Least Prime-Modulus Periods of Even-Index Fubini Numbers"),
        Blocks(
            Paragraph(Text("The source is OEIS A249938, revision 76, COMMENTS and FORMULA "
                + "blocks, an electronic entry without page numbers. Its finite formula is: "
                + "a(n) = Sum_{k=0..2*n} k! * Stirling2(2*n, k) for n>=0. "
                + "The example explicitly uses n>0. Here p is a natural prime and n "
                + "ranges over natural numbers, so the sequence argument n+1 expresses "
                + "exactly the positive indices.")),
            Paragraph(Text("StirlingTransformTotientPeriod.T at weight one and argument "
                + "2*n is the integer sum of k! times Nat.stirlingSecond (2*n) k, "
                + "for k from zero through 2*n. IsLeastPositivePeriodMod p w L means "
                + "0<L, equality of the ZMod p reductions of w(n+L) and w(n) for every "
                + "natural n, and L at most every positive t with that same equality "
                + "for every n. Nat.card counts the subtype of nonzero squares, "
                + "including 1 for p=2. The slashes in the subtype are Lean's subtype "
                + "separator. The arrow in the function is a typed lambda.")),
            Node("claim", "Provvedi's prime-modulus assertion",
                Disp(Equality(F.Id("claim"), Parenthesized(ClaimBody()))),
                SourceSentence + " The prime clause is expressed with the positive-index "
                + "sequence and the cardinality of nonzero squares. The composite-modulus "
                + "clause and the separate divisibility-by-288 conjecture are outside "
                + "this proposition. The centered dot denotes Lean's anonymous binder _.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The exact least positive period", Disp(ClaimBody()),
                "Pair opposite residues in the finite exponential representation. "
                + "The square frequency (i+1)^2 has weight 2^(-(i+1))+2^i, which "
                + "vanishes exactly when 4^(i+1)=-2. For p at least 7, three "
                + "disjoint cyclic translates bound the vanishing weights by a third "
                + "of all frequencies; both weights survive at p=5. Vandermonde "
                + "uniqueness and a polynomial root bound then force every positive "
                + "period to be at least (p-1)/2. The same number is a period. "
                + "At p=2 and p=3 the positive-index sequences are constant 1 and "
                + "constant 0, respectively, and their least positive period is one. "
                + "The centered dot denotes Lean's anonymous binder _.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("provvedi-even-fubini-" + name),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody() => All("p", Naturals(),
        Implication(App(Qualified("Nat", "Prime"), F.Id("p")),
            App(Qualified("SomerUniformSubsequenceRefutation", "IsLeastPositivePeriodMod"),
                F.Id("p"), SequenceFunction(), SquareCount())));

    private static Formula SequenceFunction() => Parenthesized(Seq(
        Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(
            F.Id("n"), Sp, Colon, Sp, Naturals())), Sp, Mapsto, Sp,
        App(Qualified("StirlingTransformTotientPeriod", "T"),
            Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
                Parenthesized(Seq(new Formula.Placeholder(), Sp, Colon, Sp, Naturals())),
                Sp, Mapsto, Sp, D(1))),
            Multiply(D(2), Add(F.Id("n"), D(1))))));

    private static Formula SquareCount() => App(Qualified("Nat", "card"),
        Seq(OpenBrace, F.Id("x"), Sp, Colon, Sp, Call("ZMod", F.Id("p")),
            Sp, Slash, Slash, Sp,
            F.Id("x"), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Call("IsSquare", F.Id("x")), CloseBrace));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) => Seq(
        Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Qualified(string owner, string name) => Seq(
        Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Seq(Operatorname, Grp(F.Id(name))), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equality(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Implication(Formula left, Formula right) =>
        Seq(left, Sp, Implies, Sp, right);
}
