using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CollinearTripleCountDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/CollinearTripleCountDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/bala2025a146557");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's square-divisibility conjecture holds for Alekseyev's A146557 formula.",
        H("Square Divisibility of the Collinear-Triple Formula"),
        Blocks(
            Paragraph(Text(
                "The Lean sequence is defined by Max Alekseyev's formula in OEIS A146557. "
                + "The identification of that formula with the geometric count is the OEIS "
                + "author's formula and is not re-proved here. Ordered matrix triples and "
                + "unordered geometric triples differ by a factor of six; neither counting "
                + "interpretation is a formal claim of this module. Peter Bala stated the "
                + "divisibility conjecture on July 24, 2025.")),
            Paragraph(Text(
                "Indices and triple coordinates are natural numbers. The functions fst "
                + "and snd are the two product projections, so a triple has type "
                + "N times (N times N). The function range(m) is the finite set of natural "
                + "numbers strictly below m. The gcd values are natural numbers, coerced "
                + "to integers in summand. All arithmetic in summand, a, and the three "
                + "theorem conclusions is integer arithmetic; the hypothesis that three "
                + "does not divide n is natural-number divisibility.")),
            Node("triples", "Positive three-part compositions", TriplesFormula(),
                "The finite product supplies all three coordinates from zero through n. "
                + "Filtering retains precisely the positive coordinates whose sum is n.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("summand", "Alekseyev's symmetric summand", SummandFormula(),
                "The three subtractions take place in the integers. Cyclically permuting "
                + "the coordinates preserves the nested gcd and permutes the subtracted terms.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The formula-defined sequence", SequenceFormula(),
                "The sequence is n times the sum of summand multiplied by the third "
                + "coordinate. This is a definition by Alekseyev's formula, not a proof "
                + "that the formula enumerates geometric triples.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("three_mul_a_eq", "The cyclic moment identity", MomentFormula(),
                "The map (i,j,k) to (j,k,i) preserves the finite composition set and has "
                + "inverse (i,j,k) to (k,i,j). Reindexing by this explicit bijection "
                + "equates the three coordinate-weighted sums. Adding them replaces the "
                + "coordinate weight by i+j+k=n, and multiplying by n gives the identity. "
                + "This reindexing is the new intermediate fact on the main proof path.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("three_dvd_summand_sum", "The symmetric total is divisible by three",
                Conditional(Divides(D(3), Total())),
                "The moment identity shows that three divides n squared times the "
                + "symmetric total. Since three is prime and does not divide n, it is "
                + "coprime to n squared. Mathlib's integer Euclid lemma therefore gives "
                + "divisibility of the total. This avoids an unnecessary totient expansion.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("sq_dvd_a", "Bala's conjecture for the formula-defined sequence",
                Conditional(Divides(Square(N()), Call("a", N()))),
                "Write the symmetric total as three times an integer quotient. "
                + "Substitution in the cyclic moment identity and cancellation of three "
                + "expresses a(n) as n squared times that quotient. The theorem holds "
                + "for every natural n not divisible by three, without a search bound.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a146557-collinear-triple-square-divisibility"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a146557-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula TriplesFormula()
    {
        Formula range = Call("range", Add(N(), D(1)));
        Formula product = Seq(range, Sp, Times, Sp,
            Parenthesized(Seq(range, Sp, Times, Sp, range)));
        Formula predicate = Seq(
            Parenthesized(Less(D(0), First())), Sp, Land, Sp,
            Parenthesized(Less(D(0), Second())), Sp, Land, Sp,
            Parenthesized(Less(D(0), Third())), Sp, Land, Sp,
            Parenthesized(Equal(Add(Add(First(), Second()), Third()), N())));
        return Disp(Seq(BoundN(), Sp, Equal(Call("triples", N()), Seq(
            OpenBrace, Triple(), Sp, InMacro, Sp, product, Sp, Mid, Sp,
            predicate, CloseBrace))));
    }

    private static Formula SummandFormula() => Disp(Seq(
        BoundN(), Sp, Forall, Sp, Triple(), Colon, Sp,
        Naturals(), Sp, Times, Sp, Parenthesized(Seq(Naturals(), Sp, Times, Sp, Naturals())),
        Comma, Sp, Equal(Call("summand", N(), Triple()),
            Add(Subtract(Subtract(Subtract(
                Multiply(N(), Call("gcd", Call("gcd", First(), Second()), Third())),
                Call("gcd", First(), N())), Call("gcd", Second(), N())),
                Call("gcd", Third(), N())), D(2)))));

    private static Formula SequenceFormula() => Disp(Seq(BoundN(), Sp,
        Equal(Call("a", N()), Multiply(N(), CompositionSum(
            Multiply(Call("summand", N(), Triple()), Third()))))));

    private static Formula MomentFormula() => Disp(Seq(BoundN(), Sp,
        Equal(Multiply(D(3), Call("a", N())), Multiply(Square(N()), Total()))));

    private static Formula Conditional(Formula conclusion) => Disp(Seq(
        BoundN(), Sp, Neg, Sp, Parenthesized(Divides(D(3), N())),
        Sp, Implies, Sp, conclusion));

    private static Formula CompositionSum(Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(Triple(), Sp, InMacro, Sp, Call("triples", N()))),
        Sp, Parenthesized(body));
    private static Formula Total() => CompositionSum(Call("summand", N(), Triple()));
    private static Formula N() => F.Id("n");
    private static Formula Triple() => F.Id("triple");
    private static Formula First() => Call("fst", Triple());
    private static Formula Second() => Call("fst", Call("snd", Triple()));
    private static Formula Third() => Call("snd", Call("snd", Triple()));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BoundN() => Seq(Forall, Sp, N(), Colon, Sp, Naturals(), Comma);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
}
