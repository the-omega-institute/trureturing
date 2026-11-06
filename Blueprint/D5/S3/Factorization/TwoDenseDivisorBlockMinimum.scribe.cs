using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TwoDenseDivisorBlockMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/TwoDenseDivisorBlockMinimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first maximal two-dense divisor block has minimum cardinality.",
        H("Minimum Length of a Two-Dense Divisor Block"),
        Blocks(
            Paragraph(Text("The target is Omar E. Pol's OEIS A401248 Conjecture 1: "
                + "a(n)=A384222(n,1). The complete increasing list contains every positive "
                + "divisor once. Adjacent a,b remain joined when b is at most twice a; "
                + "only a strict excess splits them. All positive integers are included. "
                + "At n=1 the sole block is the singleton containing one. No squarefree, "
                + "parity or finite cutoff assumption enters the statement.")),
            Paragraph(Text("The dense/rough divisor decomposition is prior mathematics: "
                + "Weingartner, arXiv:1405.2585v3, Lemma 3 with theta(u)=2u and the "
                + "t-dense characterization on pages 2-3. The implementation chooses a "
                + "largest interval-dense divisor instead of introducing an ordered "
                + "prime-power prefix as an additional representation. This is not a "
                + "claim of novelty for those ingredients.")),
            Node("divisorBlocks", "The actual maximal blocks", BlocksFormula(),
                "Use the same complete divisor list and splitBy predicate as the existing "
                + "palindromic row. Equality at ratio two stays connected.",
                DescribeRole.Definition),
            Node("claim", "The unrestricted event", ClaimFormula(),
                "For every positive n, compare the first row entry with the length of "
                + "each actual maximal block. Positive n guarantees a nonempty list; "
                + "the headD zero default adds no premise or cutoff.", DescribeRole.Definition),
            Node("block_card_ge_of_dense_factor", "A full dense copy in each block",
                DenseFactorFormula(false),
                "Assume positive coprime u,v and a dense divisor list for u. For any "
                + "member d of a block of uv, write d=gcd(d,u)gcd(d,v). Multiplying the "
                + "whole divisor list of u by gcd(d,v) gives a dense list of divisors of "
                + "uv containing d. Strict full-list gaps cannot split that copy. "
                + "Cancellation makes the map injective, so its cardinality bounds the "
                + "block length below. The separation argument is extracted from the "
                + "theorem-local connectivity proof in TwoDenseDivisorBlockMaximum.",
                DescribeRole.Theorem),
            Node("first_block_min_of_dense_factor", "The dense and rough factors",
                DenseFactorFormula(true),
                "If every prime dividing v exceeds 2u, every divisor outside D(u) also "
                + "exceeds 2u. Sortedness and splitBy's exact append law identify D(u) "
                + "as the first block. Its length is tau(u), and the copy bound applies "
                + "to every other block.", DescribeRole.Theorem),
            Node("result", "The first block is minimal", Disp(F.Id("claim")),
                "Integer interval density means that for each positive x<u there is "
                + "a divisor d with x<d<=2x. It is preserved on multiplying u by any "
                + "positive p<=2u: use an old divisor when x<u, use p when u<=x<p, "
                + "and otherwise scale a divisor above floor(x/p). Choose the largest "
                + "interval-dense divisor u of n, which exists because one qualifies. "
                + "Any prime p dividing n/u must exceed 2u, since otherwise up would "
                + "be a larger qualifying divisor. Such a prime cannot divide u, so "
                + "u and n/u are coprime. Interval coverage implies the actual sorted "
                + "divisor list has no ratio exceeding two. Apply the dense/rough "
                + "factor theorem to obtain the exact all-positive-n event.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("two-dense-minimum-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args)
    {
        var pieces = new List<Formula>();
        foreach (var arg in args)
        {
            if (pieces.Count > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arg);
        }
        return Seq(Named(name), Open, Seq(pieces.ToArray()), Close);
    }
    private static Formula DenseRelation() => Seq(Open, F.Id("a"), Comma, F.Id("b"),
        Sp, Mapsto, Sp, Call("decide", Seq(F.Id("b"), Sp, Le, Sp, D(2), Cdot, F.Id("a"))), Close);
    private static Formula DenseFactorFormula(bool first)
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var uv = Seq(u, Cdot, v);
        var positive = Seq(D(0), Lt, u, Sp, Land, Sp, D(0), Lt, v);
        var dense = Call("IsChain", Call("map", Named("fst"),
            Call("divisorsAntidiagonalList", u)), DenseRelation());
        var premise = Seq(positive, Sp, Land, Sp, Call("Coprime", u, v), Sp, Land, Sp, dense);
        if (first)
        {
            var p = F.Id("p");
            premise = Seq(premise, Sp, Land, Sp, Open, Forall, Sp, p, Comma, Sp,
                Call("Prime", p), Sp, Land, Sp, Call("dvd", p, v), Sp, Implies, Sp,
                D(2), Cdot, u, Sp, Lt, Sp, p, Close);
        }
        var lower = first ? Call("headD", Call("row", uv), D(0))
            : Call("card", Call("divisors", u));
        return Disp(Seq(Forall, Sp, u, Comma, v, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
            Comma, Sp, premise, Sp, Implies, Sp, Forall, Sp, F.Id("B"), Sp, InMacro, Sp,
            Call("divisorBlocks", uv), Comma, Sp, lower, Sp, Le, Sp, Call("length", F.Id("B"))));
    }
    private static Formula BlocksFormula() => Disp(Seq(
        Call("divisorBlocks", F.Id("n")), Sp, Eq, Sp,
        Call("splitBy", DenseRelation(),
            Call("map", Named("fst"), Call("divisorsAntidiagonalList", F.Id("n"))))));
    private static Formula ClaimFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("n"), Sp, Implies, Sp,
        Forall, Sp, F.Id("B"), Sp, InMacro, Sp, Call("divisorBlocks", F.Id("n")), Comma, Sp,
        Call("headD", Call("row", F.Id("n")), D(0)), Sp, Le, Sp,
        Call("length", F.Id("B"))));
}
