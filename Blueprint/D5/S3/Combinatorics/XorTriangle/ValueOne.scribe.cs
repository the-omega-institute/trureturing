using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.XorTriangle;

internal sealed class ValueOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/XorTriangle/ValueOne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kagey2020a334595");
    private static readonly LibraryNoteRef Reconstruction =
        LibraryNoteRef.Create("D5/L/Digit/bogdanov2020xortriangle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive natural number, the right edge of its binary XOR triangle has value one exactly when the input is a power of two.",
        H("Value One in the Binary XOR Triangle"),
        Blocks(
            Definition("differences", "Adjacent XOR", DifferencesFormula(),
                "Peter Kagey's OEIS A334595, revision 18, defines the triangle: \"An XOR-triangle is an inverted 0-1 triangle formed by choosing a top row and having each entry in the subsequent rows be the XOR of the two values above it.\" A row is a list of Boolean bits. The function differences preserves their order and replaces each adjacent pair by ordinary Boolean XOR. Empty rows and one-bit rows have empty differences.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("leftEdge", "The retained left edge", LeftEdgeFormula(),
                "leftEdge(k, xs) records k entries from the first element of xs down through successive difference rows. The default head of an empty row is false. In the right-edge construction k is the original row length, so every recorded row is nonempty. All k edge positions are retained, including zero bits.",
                AssessedProvenance.FromRepo(Source)),
            Definition("sourceRow", "The unpadded binary input", SourceRowFormula(),
                "The source's name is \"Binary interpretation of the right diagonal of the XOR-triangle with first row generated from the binary expansion of n.\" Lean's Nat.bits lists bits from least significant to most significant; sourceRow reverses it to obtain the unpadded most-significant-first row. No zeros are added to the input. The theorem uses positive n, including n equal to one.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("rightEdge", "Right edge from the top to the apex", RightEdgeFormula(),
                "The source fixes the orientation with n equal to 19: \"Reading the right side of the triangle starting from the upper-right corner gives 10100 which is the binary representation of 20 = a(19).\" Reversing the original row turns its right edge into a left edge because Boolean XOR is symmetric. rightEdge retains the original number of positions and reads from the top-right corner to the apex; leading zero bits of the edge are retained.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("decode", "Binary decoding with the width retained", DecodeFormula(),
                "decode interprets a Boolean row as a most-significant-first binary word. It reverses the row, maps false to zero and true to one, and passes those least-significant-first digits to Nat.ofDigits with base two. The row itself retains its full width even when its value has a shorter canonical binary expansion.",
                AssessedProvenance.FromRepo(Source)),
            Definition("a", "The sequence A334595", SequenceFormula(),
                "The source row, ordinary adjacent XOR, top-right-to-apex edge and binary decoding define a(n). For the source's n equal to 19, the row is 10011 and the right edge is 10100, giving a(19) equal to 20. For n equal to one the row and edge each consist of the single bit one. The definition is total on natural numbers; the classification below is restricted to positive inputs.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("xortriangle-value-one-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The value-one classification"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source, Reconstruction),
                Blocks(Paragraph(Text(
                    "The fourth %C comment of OEIS A334595, revision 18, is the second conjecture: \"Conjecture: a(n) = 1 if and only if n is a power of two.\" For every natural n at least one, with the unpadded most-significant-first input and all right-edge positions retained, a(n) equals one if and only if there exists a natural k such that n equals 2 to the power k. The exponent may be zero, so n equal to one is included. The proof reconstructs a fixed-width row from its edge and establishes injectivity. At that same width, the word with only its final bit equal to one decodes to one; its unique source row has only its first bit equal to one and decodes to a power of two. The finite-XOR reconstruction uses the reversible-triangle relation also used by Ilya Bogdanov in MathOverflow answer 359278, revision 5. The quoted OEIS text and adapted reversible-triangle argument are attributed to Peter Kagey, the OEIS Foundation and Ilya Bogdanov under CC BY-SA 4.0; the Library notes identify the sources and adaptations. The result is proved within Lean without an invertibility premise or a literature axiom. The record-position conjecture and rotational fixed-point counting are separate assertions."))),
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Definition(string declaration, string title,
        Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("xortriangle-value-one-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula BoolType() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula WordType() => Call("List", BoolType());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Cons(Formula bit, Formula rest) => Call("cons", bit, rest);
    private static Formula Nil() => Named("nil");

    private static Formula DifferencesFormula()
    {
        Formula b = F.Id("b"), c = F.Id("c"), xs = F.Id("xs");
        return Disp(new Formula.Aligned([
            Equal(Call("differences", Nil()), Nil()),
            All("b", BoolType(), Equal(Call("differences", Call("singleton", b)), Nil())),
            All("b", BoolType(), All("c", BoolType(), All("xs", WordType(),
                Equal(Call("differences", Cons(b, Cons(c, xs))),
                    Cons(Call("xor", b, c), Call("differences", Cons(c, xs)))))))
        ]));
    }

    private static Formula LeftEdgeFormula()
    {
        Formula k = F.Id("k"), xs = F.Id("xs");
        return Disp(new Formula.Aligned([
            All("xs", WordType(), Equal(Call("leftEdge", D(0), xs), Nil())),
            All("k", NatType(), All("xs", WordType(),
                Equal(Call("leftEdge", new Formula.Binary(k, FormulaBinaryOperator.Add, D(1)), xs),
                    Cons(Call("headD", xs, Named("false")),
                        Call("leftEdge", k, Call("differences", xs))))))
        ]));
    }

    private static Formula SourceRowFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", NatType(), Equal(Call("sourceRow", n), Call("reverse", Call("bits", n)))));
    }

    private static Formula RightEdgeFormula()
    {
        Formula row = F.Id("row");
        return Disp(All("row", WordType(), Equal(Call("rightEdge", row),
            Call("leftEdge", Call("length", row), Call("reverse", row)))));
    }

    private static Formula DecodeFormula()
    {
        Formula row = F.Id("row");
        return Disp(All("row", WordType(), Equal(Call("decode", row),
            Call("ofDigits", D(2), Call("map", Named("BoolToNat"), Call("reverse", row))))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", NatType(), Equal(Call("a", n),
            Call("decode", Call("rightEdge", Call("sourceRow", n))))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        Formula powerOfTwo = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("k"), NatType(), Equal(n, new Formula.Power(D(2), k)));
        Formula equivalence = new Formula.Logic(Equal(Call("a", n), D(1)),
            FormulaLogicOperator.Iff, Parenthesized(powerOfTwo));
        return Disp(All("n", NatType(), new Formula.Logic(Parenthesized(positive),
            FormulaLogicOperator.Implies, Parenthesized(equivalence))));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
