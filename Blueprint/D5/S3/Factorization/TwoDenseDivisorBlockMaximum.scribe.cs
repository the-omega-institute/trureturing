using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TwoDenseDivisorBlockMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/TwoDenseDivisorBlockMaximum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/pol2026a400194");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest two-dense divisor block has ruler-scaled maximum odd count.",
        H("Maximum Length of a Two-Dense Divisor Block"),
        Blocks(
            Paragraph(Text("Both statistics use the complete increasing list of positive "
                + "divisors and its actual maximal splitBy blocks. An adjacent pair a,b "
                + "stays joined exactly when b is at most twice a. Equality and singleton "
                + "blocks are retained. The theorem includes every positive natural n.")),
            Node("oddBlockCounts", "Odd counts in the actual blocks", OddCountsFormula(),
                "Count odd entries in each block of the same partition used by the "
                + "existing row function. At n=0 Mathlib's divisor list is empty.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("result", "The maximum identity", ResultFormula(),
                "Sortedness and the strict separating boundaries show that divisor-list "
                + "endpoints whose ratio is at most two have the same block membership. "
                + "Every complete dyadic chain of an odd divisor therefore remains inside "
                + "one actual block. The map from an odd member and an exponent between "
                + "zero and factorization(n,2) to their dyadic product bijects onto that "
                + "block. Odd-component recovery, cancellation and injectivity of powers "
                + "of two prove injectivity. Distinct divisor entries turn the bijection "
                + "into the local block-length identity. Taking suprema over the same "
                + "block family gives the conjectured maximum formula. The zero default "
                + "of the natural supremum is harmless; every positive n has divisor one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a400194-two-dense-divisor-block-maximum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("two-dense-maximum-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var pieces = new List<Formula>();
        foreach (var arg in args)
        {
            if (pieces.Count > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arg);
        }
        return Seq(Named(name), Parenthesized(Seq(pieces.ToArray())));
    }
    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Colon, Sp, Nat(), Comma, Sp, body));
    private static Formula Positive(Formula body) => Universal(Seq(
        D(0), Sp, Lt, Sp, N(), Sp, Implies, Sp, body));
    private static Formula Divisors() => Call("map", Named("fst"),
        Call("divisorsAntidiagonalList", N()));
    private static Formula Parts() => Call("splitBy",
        Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Mapsto, Sp,
            Call("decide", Seq(F.Id("b"), Sp, Le, Sp, D(2), Cdot, Sp, F.Id("a"))))),
        Divisors());
    private static Formula OddCount() => Call("length", Call("filter",
        Parenthesized(Seq(F.Id("d"), Sp, Mapsto, Sp,
            Call("decide", Call("Odd", F.Id("d"))))), F.Id("B")));
    private static Formula OddCountsFormula() => Universal(Seq(
        Call("oddBlockCounts", N()), Sp, Eq, Sp, Call("map",
            Parenthesized(Seq(F.Id("B"), Sp, Mapsto, Sp, OddCount())), Parts())));
    private static Formula Maximum(string row) => Call("sup",
        Call("toFinset", Call(row, N())), Named("id"));
    private static Formula ResultFormula() => Positive(Seq(
        Maximum("row"), Sp, Eq, Sp,
        Parenthesized(Seq(Call("factorization", N(), D(2)), Sp, Plus, Sp, D(1))),
        Sp, Cdot, Sp, Maximum("oddBlockCounts")));
}
