using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class RectangularDeltaChainDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Lattices/RectangularDeltaChain.";
    private static readonly LibraryNoteRef Derivation =
        LibraryNoteRef.Create("D5/L/ArithSums/codex2026rectangulardeltachain");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer progression in a finite rectangle has an attained maximum length.",
        H("Longest Integer Chains in a Rectangle"),
        Paragraph(Text(
            "Let P be a finite coordinate set, L a family of natural side lengths, and d an "
            + "integer direction. A chain of n points from a has coordinates a(p) + j d(p) "
            + "between zero and L(p) for every j in {0,...,n-1} and every p. Unless stated "
            + "otherwise, assume explicitly that some coordinate of d is nonzero.")),
        Paragraph(Text(
            "Write M for one plus the minimum of floor(L(p)/|d(p)|) over the nonzero "
            + "coordinates. The corner c has c(p)=L(p) if d(p)<0 and c(p)=0 otherwise. "
            + "Lengths count points, including the initial point; the empty chain has length zero.")),
        Blocks(
            Describe.Lean(
                DescribeId.Create("delta-chain-coordinate-bound"),
                DeclarationHandle.Create(Module + "chain_length_le_coordinate"),
                H("Each moving coordinate bounds the point count"),
                StatementSource.FromAuthor(Disp(Seq(Chain("a", "n"), Sp, Land, Sp,
                    At("d"), Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("n"), Sp, Le, Sp, D(1), Plus, Quotient()))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "For any chosen p with d(p) nonzero, the difference between the first "
                    + "and last points has magnitude (n-1)|d(p)| and cannot exceed L(p). "
                    + "The empty chain also satisfies the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-chain-minimum-bound"),
                DeclarationHandle.Create(Module + "chain_length_le"),
                H("The smallest coordinate quotient bounds every chain"),
                StatementSource.FromAuthor(Disp(Seq(Chain("a", "n"), Sp, Rightarrow, Sp,
                    F.Id("n"), Sp, Le, Sp, F.Id("M")))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "Applying the coordinate bound to every moving coordinate and taking "
                    + "their finite minimum gives the common upper bound M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-chain-corner-attainment"),
                DeclarationHandle.Create(Module + "corner_chain"),
                H("The sign-selected corner attains the bound"),
                StatementSource.FromAuthor(Disp(Chain("c", "M"))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "For j<M each displacement magnitude j|d(p)| is at most L(p). "
                    + "Positive coordinates increase from zero, negative coordinates "
                    + "decrease from L(p), and zero coordinates remain zero. Every one "
                    + "of these M points therefore lies in the rectangle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-chain-length-characterization"),
                DeclarationHandle.Create(Module + "exists_chain_iff"),
                H("Exactly the lengths up to M occur"),
                StatementSource.FromAuthor(Disp(Seq(Open, Exists, Sp, F.Id("a"), Comma, Sp,
                    Chain("a", "n"), Close, Sp, Iff, Sp, F.Id("n"), Sp, Le, Sp, F.Id("M")))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "Every shorter length is obtained by taking an initial segment of "
                    + "the corner chain; the upper bound excludes all larger lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-chain-maximum-length"),
                DeclarationHandle.Create(Module + "longest_chain_length"),
                H("The greatest attainable point count"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("mmax"), Sp, Eq, Sp, D(1), Plus,
                    Operatorname, Grp(F.Id("min")), Underscore,
                    Grp(At("d"), Sp, Neq, Sp, D(0)), Sp, Quotient()))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "The theorem asserts that M is the greatest element of the set of "
                    + "attainable chain lengths: it belongs to that set and bounds every "
                    + "member. Attainment and the universal bound concern the same "
                    + "rectangle and direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delta-chain-zero-direction"),
                DeclarationHandle.Create(Module + "zero_direction_unbounded"),
                H("Zero direction admits every sequence length"),
                StatementSource.FromAuthor(Disp(Seq(Open, Forall, Sp, F.Id("p"), Comma, Sp,
                    At("d"), Sp, Eq, Sp, D(0), Close, Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("n"), Comma, Sp, Chain("0", "n")))),
                AssessedProvenance.FromRepo(Derivation),
                Blocks(Paragraph(Text(
                    "If every direction component is zero, the sequence based at the "
                    + "lower corner satisfies the window bounds for every natural length. "
                    + "These sequences repeat one point, which explains the explicit "
                    + "nonzero-coordinate hypothesis in the maximum-length formula."))),
                DescribeRole.Theorem))));

    private static Formula At(string name) => Seq(F.Id(name), Underscore, Grp(F.Id("p")));

    private static Formula Quotient() => Seq(Lfloor, Sp, Frac, Grp(At("L")),
        Grp(Vert, Sp, At("d"), Sp, Vert), Sp, Rfloor);

    private static Formula Chain(string start, string length) => Seq(
        Operatorname, Grp(F.Id("Chain")), Open, F.Id("L"), Comma, F.Id("d"), Comma,
        start == "0" ? D(0) : F.Id(start), Comma, F.Id(length), Close);
}
