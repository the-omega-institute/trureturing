using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class YanevRunCompressionClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/YanevRunCompressionClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/yanev2016a090079");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary run compression satisfies Yanev's formula at every natural index, including zero.",
        H("Yanev's Binary Run Compression Formula"),
        Blocks(
            Paragraph(Text("The variable n ranges over the natural numbers N, including zero. "
                + "The operator digits_2(n) is Nat.digits 2 n, the little-endian binary digit "
                + "list, with the empty list at zero. The operator ofDigits_2 decodes a "
                + "little-endian list using Nat.ofDigits 2. Boolean equality on naturals is "
                + "denoted by beq; splitBy(beq,l) partitions a list l into maximal contiguous "
                + "equal-digit blocks, in their original order. The operator head! denotes "
                + "List.head!, returning the first entry of a nonempty list and zero on the "
                + "empty list. The operator map applies a function to every list entry, "
                + "and length denotes List.length. Thus runs(n) counts blocks and a(n) "
                + "decodes their heads. The operator mod is natural-number remainder. "
                + "Addition, multiplication, and powers are on naturals, and subtraction "
                + "is truncated natural subtraction.")),
            Node("runs", "The number of binary runs", RunsFormula(),
                "Every block is nonempty. The block count is the number of maximal "
                + "constant runs, unchanged by reversing the digit order. At zero it is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "Literal run compression", CompressionFormula(),
                "Keeping one head per block replaces each nonempty run of zeros or ones "
                + "by one copy of that digit. Little-endian decoding implements the "
                + "operation in the OEIS NAME. The empty digit list gives a(0)=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Yanev's closed form", ResultFormula(),
                "The cited formula uses A005811(n) for the number of binary runs. "
                + "Its integer parity term (1-(-1)^n)/2 = n mod 2. The statement is "
                + "multiplied by 3 to stay in N. For nonzero n the compressed word "
                + "alternates, has binary entries, and ends in one. The proof instantiates "
                + "the digit and splitBy APIs and normalizes using the inlined "
                + "alternating-list evaluation identity; its head is n mod 2. "
                + "The zero case follows from the definitions.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a090079-yanev-run-compression-closed-form"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a090079-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula BinaryCall(string name, Formula argument) =>
        new Formula.Apply(new Formula.Subscript(Named(name), D(2)), [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Universal(Formula n, Formula body) =>
        Disp(Seq(Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp, body));
    private static Formula RunBlocks(Formula n) =>
        Call("splitBy", Named("beq"), BinaryCall("digits", n));

    private static Formula RunsFormula()
    {
        Formula n = F.Id("n");
        return Universal(n, Equal(Call("runs", n), Call("length", RunBlocks(n))));
    }

    private static Formula CompressionFormula()
    {
        Formula n = F.Id("n");
        return Universal(n, Equal(Call("a", n),
            BinaryCall("ofDigits", Call("map", Seq(Operatorname, Grp(F.Id("head"), Bang)), RunBlocks(n)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula power = new Formula.Power(D(2), Parenthesized(Add(Call("runs", n), D(1))));
        return Universal(n, Equal(Mul(D(3), Call("a", n)),
            Subtract(Parenthesized(Add(power, Call("mod", n, D(2)))), D(2))));
    }
}
