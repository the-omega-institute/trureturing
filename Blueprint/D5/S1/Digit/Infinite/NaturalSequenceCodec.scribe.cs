using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class NaturalSequenceCodecDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/NaturalSequenceCodec.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary natural sequences have literal legal paired unary names and executable prefix recovery.",
        H("Natural sequences as legal infinite digits"),
        Blocks(
            Node("block", "Finite blocks", DescribeRole.Definition,
                "For every natural a, block(a) is a copies of the two bits 10 followed by 00. "
                + "In particular, block(0) is 00. Lists retain all zeros and repeated delimiters."),
            Node("encodedPrefix", "Concatenated initial blocks", DescribeRole.Definition,
                "For a sequence p of arbitrary natural numbers, encodedPrefix(p,n) concatenates "
                + "block(p(0)) through block(p(n-1)) in that order. It is empty for n=0. "
                + "Write B(p,n) for this list and length for the number of bits in a list."),
            Node("encode", "The infinite legal code", DescribeRole.Definition,
                "The unary word writeNat(a) consists of a ones followed by a zero. Concatenating "
                + "these nonempty words gives an infinite unary stream. Encoding replaces each "
                + "unary bit b by the pair b0. Thus E(p)=encode(p) is the literal infinite "
                + "concatenation of the blocks. Every odd numbered bit, indexed from zero, is zero; "
                + "each adjacent pair of positions contains such a bit. The value belongs to "
                + "SuccessorContinuity.LegalDigits, the existing subtype of streams with no adjacent ones. "
                + "Random access terminates by decreasing the requested unary index whenever a whole "
                + "block is skipped. It applies to zero entries and arbitrarily long blocks."),
            Node("parsePrefix", "Finite unary parsing", DescribeRole.Definition,
                "Given a natural count n and a finite Boolean list, parsePrefix reads n unary "
                + "numbers using readNat and returns their list, or none if a complete prefix is "
                + "unavailable. It ignores the unused suffix. For n=0 it returns the empty list."),
            Node("decodePrefix", "Decoding with finite fuel", DescribeRole.Definition,
                "decodePrefix(x,n,fuel) reads the first bit of each of fuel consecutive pairs "
                + "of x, then calls parsePrefix. It queries only the positions 2j for j less than "
                + "fuel. On an encoded stream, any fuel containing the first n complete blocks "
                + "succeeds. A successful result persists when the input window is extended. "
                + "Only recovery on the image is asserted; odd bits are not checked by this parser."),
            Node("recoverPrefix", "Executable search on the image", DescribeRole.Definition,
                "For x accompanied by a proof that x is in the image of encode, recoverPrefix(x,n) "
                + "tests increasing finite fuel until decodePrefix succeeds and returns its result. "
                + "The implementation uses the computable Nat.find search. Its termination proof "
                + "and the image membership proof are erased during execution: no preimage sequence "
                + "is supplied as runtime data. Write R(x,n) for this proof independent result, "
                + "and take(n,s) for the first n entries of a stream s. Computability here is "
                + "relative to access to the input sequence or stream; no claim makes an arbitrary "
                + "noncomputable sequence into a finite computable program."),
            Describe.Lean(
                DescribeId.Create("natural-sequence-codec-transport"),
                DeclarationHandle.Create(Prefix + "natural_sequence_transport"),
                H("Literal transport and complete prefix recovery"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural sequence p, every finite block concatenation is exactly "
                        + "an initial segment of E(p), and its length is at least twice its block count. "
                        + "The lengths are therefore unbounded. Every finite prefix of p is recovered "
                        + "from E(p). Equality E(p)=E(q) forces equality of all finite source prefixes, "
                        + "hence p=q. Legality is also part of the codomain of encode.")),
                    Paragraph(Text(
                        "For each requested n, the finite concatenation of the first n unary words "
                        + "has finite length. At that fuel the existing identity readNat_writeNat "
                        + "recovers each entry in turn. The stream expansion identifies that finite "
                        + "word with the even positions of the actual infinite code. The identity "
                        + "readNat_eq_some shows that successful parsing consumes exactly its unary "
                        + "prefix, so extra input cannot change a successful answer. Extending any "
                        + "successful window to a window containing n full blocks proves soundness "
                        + "of the first successful search result. The proof uses this actual recovery "
                        + "to distinguish arbitrary source sequences."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("natural-sequence-codec-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula NatSequence => Seq(NatType, Sp, To, Sp, NatType);
    private static Formula Group(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);

    private static Formula TransportFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula b = Call("B", p, n);
        Formula e = Call("E", p);
        Formula length = Call("length", b);
        return Disp(All("p", NatSequence, Seq(
            Group(All("n", NatType, Seq(
                Call("take", length, e), Sp, Eq, Sp, b, Sp, Land, Sp,
                D(2), n, Sp, Leq, Sp, length))), Sp, Land, Sp,
            Group(All("n", NatType, Seq(Call("R", e, n), Sp, Eq, Sp,
                Call("take", n, p)))), Sp, Land, Sp,
            Group(All("q", NatSequence, Seq(e, Sp, Eq, Sp, Call("E", q), Sp,
                Implies, Sp, p, Sp, Eq, Sp, q))))));
    }
}
