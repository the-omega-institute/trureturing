using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class AtomicPrefixParserDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal two-letter tree code has an executable recursive parser with exact suffix boundaries, injective code, prefix-free image, and complete decoding.",
        H("Literal Atomic Prefix Parser"),
        Blocks(
            Paragraph(Text("Source is the existing FreeMagma Bool of finite nonempty ordered binary trees. "
                + "The true leaf is alpha and the false leaf is beta. A leaf b is encoded as "
                + "[true,b], while a branch is encoded as false followed by the concatenation of "
                + "the left and right codes. The parser uses predecessor fuel for both recursive "
                + "children and passes the actual remainder returned by the left parse to the right parse. "
                + "Its public fuel is the input length, and decode accepts only an empty final remainder.")),
            Describe.Lean(DescribeId.Create("atomic-prefix-parser-code"),
                DeclarationHandle.Create(Prefix + "code"), H("Literal Tree Code"),
                StatementSource.FromAuthor(CodeFormula()), AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(CodeTypeFormula()),
                    Paragraph(Text("The two Boolean letters are used directly. Internal nodes begin "
                    + "with false, so the two child codes are parsed without a delimiter or integer "
                    + "encoding."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("atomic-prefix-parser-parse"),
                DeclarationHandle.Create(Prefix + "parse"), H("Fuelled Suffix Parser"),
                StatementSource.FromAuthor(ParseFormula()), AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(ParseTypeFormula()),
                    Paragraph(Text("Parsing returns either failure or a source tree together with "
                        + "the exact unconsumed suffix. The local recurrence below uses recursion-depth "
                        + "fuel: both child calls receive n, and the right child receives the actual "
                        + "left remainder r. The clauses exhaust the input shapes and recursive outcomes. "
                        + "The public parser derives its fuel from the input length.")),
                    new DocumentBlock.DisplayFormula(ParseFuelTypeFormula()), new DocumentBlock.DisplayFormula(ParseFuelZeroFormula()),
                    new DocumentBlock.DisplayFormula(ParseFuelLeafFormula()), new DocumentBlock.DisplayFormula(ParseFuelBranchFormula()),
                    new DocumentBlock.DisplayFormula(ParseFuelLeftFailureFormula()), new DocumentBlock.DisplayFormula(ParseFuelRightFailureFormula()),
                    new DocumentBlock.DisplayFormula(ParseFuelTruncationFormula())),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("atomic-prefix-parser-decode"),
                DeclarationHandle.Create(Prefix + "decode"), H("Complete Decoder"),
                StatementSource.FromAuthor(DecodeFormula()), AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(DecodeTypeFormula()),
                    Paragraph(Text("Here emptyRemainder denotes the mathematical operation defined by "
                        + "the following three cases. Decoding succeeds exactly when the parser consumes "
                        + "the whole input, and then returns the parsed source.")),
                    new DocumentBlock.DisplayFormula(EmptyRemainderTypeFormula()), new DocumentBlock.DisplayFormula(EmptyRemainderFormula())),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("atomic-prefix-parser-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Exact Parsing and Prefix-Free Coding"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first conjunct is the successful-consumption equivalence for "
                        + "every input, tree, and suffix. Its proof keeps the stronger local induction "
                        + "invariant that any successful fuelled parse consumes exactly one codeword, "
                        + "and the uniform sufficient-fuel invariant that every codeword followed by "
                        + "an arbitrary suffix parses with that suffix unchanged.")),
                    Paragraph(Text("The same parser law gives injectivity by applying a local Encoding "
                        + "roundtrip, and gives prefix freedom by parsing one complete codeword in "
                        + "two ways. Full decoding is equivalent to being exactly a codeword; malformed "
                        + "inputs and nonempty suffixes are rejected."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] xs)
    {
        var terms = new List<Formula>();
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Sp, Land, Sp));
            terms.Add(Par(xs[i]));
        }
        return Seq(terms.ToArray());
    }
    private static Formula WordType() => Seq(V("List"), Sp, V("Bool"));
    private static Formula ParseResultType() => Call("Option", Seq(V("Source"), Sp, Times, Sp, WordType()));
    private static Formula DecodeResultType() => Seq(V("Option"), Sp, V("Source"));
    private static Formula Binder(string name, Formula domain) => Par(Seq(V(name), Sp, Colon, Sp, domain));
    private static Formula All(Formula body, params Formula[] binders) => Seq(
        Forall, Sp, Seq(binders.Select((b, i) => i == 0 ? b : Seq(Sp, b)).ToArray()),
        Comma, Sp, Par(body));
    private static Formula List(params Formula[] entries) => Seq(OpenBracket,
        Seq(entries.Select((e, i) => i == 0 ? e : Seq(Comma, Sp, e)).ToArray()), CloseBracket);
    private static Formula Cons(Formula head, Formula tail) => Seq(head, Sp, Colon, Colon, Sp, tail);
    private static Formula Append(Formula left, Formula right) => Seq(left, Sp, Plus, Plus, Sp, right);
    private static Formula Pair(Formula left, Formula right) => Par(Seq(left, Comma, Sp, right));
    private static Formula SomePair(Formula tree, Formula remainder) => Call("some", Pair(tree, remainder));
    private static Formula Fuel(Formula n, Formula word) => Call("parseFuel", n, word);
    private static Formula Successor(Formula n) => Seq(n, Sp, Plus, Sp, D(1));
    private static Formula Implies(Formula premise, Formula conclusion) => Seq(Par(premise), Sp, Rightarrow, Sp, conclusion);
    private static Formula TypeOf(string name, params Formula[] types) => Disp(Seq(V(name), Sp, Colon, Sp,
        Seq(types.Select((t, i) => i == 0 ? t : Seq(Sp, To, Sp, t)).ToArray())));
    private static Formula CodeTypeFormula() => TypeOf("code", V("Source"), WordType());
    private static Formula ParseTypeFormula() => TypeOf("parse", WordType(), ParseResultType());
    private static Formula DecodeTypeFormula() => TypeOf("decode", WordType(), DecodeResultType());
    private static Formula CodeFormula() => Disp(And(
        All(Equal(Call("code", Call("of", V("b"))), List(V("true"), V("b"))), Binder("b", V("Bool"))),
        All(Equal(Call("code", Call("mul", V("s"), V("t"))),
            Cons(V("false"), Par(Append(Call("code", V("s")), Call("code", V("t")))))),
            Binder("s", V("Source")), Binder("t", V("Source")))));
    private static Formula ParseFormula() => Disp(All(
        Equal(Call("parse", V("w")), Fuel(Call("length", V("w")), V("w"))), Binder("w", WordType())));
    private static Formula ParseFuelTypeFormula() => TypeOf("parseFuel", V("Nat"), WordType(), ParseResultType());
    private static Formula ParseFuelZeroFormula() => Disp(All(
        Equal(Fuel(D(0), V("w")), V("none")), Binder("w", WordType())));
    private static Formula ParseFuelLeafFormula() => Disp(All(
        Equal(Fuel(Successor(V("n")), Cons(V("true"), Cons(V("b"), V("r")))),
            SomePair(Call("of", V("b")), V("r"))),
        Binder("n", V("Nat")), Binder("b", V("Bool")), Binder("r", WordType())));
    private static Formula ParseFuelBranchFormula() => Disp(All(
        Implies(And(Equal(Fuel(V("n"), V("w")), SomePair(V("s"), V("r"))),
                Equal(Fuel(V("n"), V("r")), SomePair(V("t"), V("q")))),
            Equal(Fuel(Successor(V("n")), Cons(V("false"), V("w"))),
                SomePair(Call("mul", V("s"), V("t")), V("q")))),
        Binder("n", V("Nat")), Binder("w", WordType()), Binder("s", V("Source")),
        Binder("r", WordType()), Binder("t", V("Source")), Binder("q", WordType())));
    private static Formula ParseFuelLeftFailureFormula() => Disp(All(
        Implies(Equal(Fuel(V("n"), V("w")), V("none")),
            Equal(Fuel(Successor(V("n")), Cons(V("false"), V("w"))), V("none"))),
        Binder("n", V("Nat")), Binder("w", WordType())));
    private static Formula ParseFuelRightFailureFormula() => Disp(All(
        Implies(And(Equal(Fuel(V("n"), V("w")), SomePair(V("s"), V("r"))),
                Equal(Fuel(V("n"), V("r")), V("none"))),
            Equal(Fuel(Successor(V("n")), Cons(V("false"), V("w"))), V("none"))),
        Binder("n", V("Nat")), Binder("w", WordType()), Binder("s", V("Source")), Binder("r", WordType())));
    private static Formula ParseFuelTruncationFormula() => Disp(All(And(
        Equal(Fuel(Successor(V("n")), List()), V("none")),
        Equal(Fuel(Successor(V("n")), List(V("true"))), V("none"))), Binder("n", V("Nat"))));
    private static Formula DecodeFormula() => Disp(All(
        Equal(Call("decode", V("w")), Call("emptyRemainder", Call("parse", V("w")))), Binder("w", WordType())));
    private static Formula EmptyRemainderTypeFormula() => TypeOf("emptyRemainder", ParseResultType(), DecodeResultType());
    private static Formula EmptyRemainderFormula() => Disp(And(
        Equal(Call("emptyRemainder", V("none")), V("none")),
        All(Equal(Call("emptyRemainder", SomePair(V("t"), List())), Call("some", V("t"))),
            Binder("t", V("Source"))),
        All(Equal(Call("emptyRemainder", SomePair(V("t"), Cons(V("b"), V("r")))), V("none")),
            Binder("t", V("Source")), Binder("b", V("Bool")), Binder("r", WordType()))));
    private static Formula ResultFormula()
    {
        var w = V("w"); var t = V("t"); var r = V("r");
        var parsing = All(Seq(Call("parse", w), Sp, Eq, Sp,
            Call("some", Par(Seq(t, Comma, r))), Sp, Leftrightarrow, Sp,
            Equal(w, Call("append", Call("code", t), r))),
            Binder("w", WordType()), Binder("t", V("Source")), Binder("r", WordType()));
        var injective = Call("Injective", V("code"));
        var prefix = Call("IsPrefixFree", Call("range", V("code")));
        var decoding = All(Seq(Call("decode", w), Sp, Eq, Sp,
            Call("some", t), Sp, Leftrightarrow, Sp, Equal(w, Call("code", t))),
            Binder("w", WordType()), Binder("t", V("Source")));
        return Disp(And(parsing, injective, prefix, decoding));
    }
}
