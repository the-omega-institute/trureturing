using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class SupernormSizeAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/SupernormSizeAsymptotic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/lagariassun2024supernorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal prime supernorms over all partitions of size n have leading term exp(gamma)/n.",
        H("Reciprocal supernorms in the size ensemble"),
        Blocks(
            Paragraph(Text("Nat denotes the nonnegative integers and Real the real numbers. "
                + "A partition of n is an unordered multiset of positive parts whose sum is n. "
                + "The source is Lagarias and Sun, arXiv:2308.15303v1: equation (3.1) defines "
                + "the size ensemble, and Conjecture 3.5 states its asymptotic.")),
            Node("partPrime", "Primes attached to positive parts", PartPrimeFormula(),
                "Nat.nth numbers the primes from zero, and Nat.sub is truncated natural "
                + "subtraction. Thus partPrime(k) is the k-th prime for every positive k, "
                + "with partPrime(1)=2. Its value at zero is also two. The source's separate "
                + "convention p_0=1 is immaterial because a partition has no zero part.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("supernorm", "The supernorm of a partition", SupernormFormula(),
                "Multiset.map retains every occurrence of a part, and Multiset.prod "
                + "multiplies all mapped occurrences. A repeated part contributes its prime "
                + "with the same multiplicity. The empty product is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Wsize", "The complete fixed-size weight", WsizeFormula(),
                "The sum contains every partition of exactly n once. The denominator is "
                + "the natural supernorm cast to Real. All prime factors are positive, "
                + "so this is precisely the source's reciprocal supernorm weight.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The size asymptotic", ResultFormula(),
                "The function n times Wsize(n) tends to exp(gamma) along all natural "
                + "indices tending to infinity, where gamma is Euler's constant. Since "
                + "exp(gamma) is positive, this is equivalent to "
                + "Wsize(n) asymptotic to exp(gamma)/n, exactly Conjecture 3.5. "
                + "No monotonicity of the individual weights is assumed. "
                + "Finite geometric products and their energy moments bound the cumulative "
                + "mass A_n between E_m(1-m/n) and E_n, where E_m is the product of "
                + "(1-1/p_j)^(-1) for 1<=j<=m. Taking m=floor(n/log n), Mertens' product "
                + "theorem and the prime number theorem give A_n/log n tending to exp(gamma). "
                + "Marking repeated parts and deleting them gives the positive convolution "
                + "n Wsize(n)=sum_{j=1}^n b_j Wsize(n-j), with "
                + "b_j=sum_{d|j} d/p_d^(j/d). Its proper-divisor remainder is at most "
                + "2 times the divisor count divided by j, hence b_j log j tends to one. "
                + "A uniform estimate on the half window gives the main term. Strong "
                + "induction bounds n Wsize(n), and Cesaro averaging makes the remaining "
                + "half convolution tend to zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lagarias-sun-2024-supernorm-size-asymptotic"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("supernorm-size-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Name(owner), Dot, Name(name));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        args.Length == 0 ? Qualified(owner, name)
            : new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Divide(Formula a, Formula b) =>
        new Formula.Fraction(a, b);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula CastReal(Formula body) =>
        Parenthesized(Seq(body, Colon, Sp, Call("Real")));
    private static Formula Partition(Formula n) => QCall("Nat", "Partition", n);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Call("fun"),
            Parenthesized(Seq(X(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));

    private static Formula PartPrimeFormula() => All("k", Call("Nat"),
        Equal(Call("partPrime", X("k")), QCall("Nat", "nth", QCall("Nat", "Prime"),
            QCall("Nat", "sub", X("k"), D(1)))));

    private static Formula SupernormFormula() => All("n", Call("Nat"),
        All("p", Partition(X("n")), Equal(Call("supernorm", X("p")),
            QCall("Multiset", "prod", QCall("Multiset", "map", Call("partPrime"),
                Call("parts", X("p")))))));

    private static Formula WsizeFormula() => All("n", Call("Nat"),
        Equal(Call("Wsize", X("n")), Seq(
            new Formula.Subscript(Sum, Seq(X("p"), Colon, Sp, Partition(X("n")))),
            Sp, Divide(D(1), CastReal(Call("supernorm", X("p")))))));

    private static Formula ResultFormula() => Call("Tendsto",
        Fun("n", Call("Nat"), Multiply(CastReal(X("n")), Call("Wsize", X("n")))),
        Call("atTop"), Call("nhds", QCall("Real", "exp",
            QCall("Real", "eulerMascheroniConstant"))));
}
