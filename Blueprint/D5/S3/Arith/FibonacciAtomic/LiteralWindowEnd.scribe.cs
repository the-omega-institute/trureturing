using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class LiteralWindowEndDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Low-to-high three-bit windows have a terminal flag as well as a seam. "
                + "Successful literal End queries correspond to independent selected positions.",
            H("Literal Windows and Positive End"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("literal-window-execution"),
                    DeclarationHandle.Create(Prefix + "execution"),
                    H("The seam guard recognizes the flattened legal word"),
                    StatementSource.FromAuthor(ExecutionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Here B is the Boolean set, W is the five-letter window alphabet, "
                                + "W* is its finite-word set, and none is the absorbing error. "
                                + "The letters are 000, 100, 010, 101 and 001 in low-to-high "
                                + "order. The final seam and End flag are the following folds; "
                                + "the initial End flag survives only for the empty word.")),
                        new DocumentBlock.DisplayFormula(ExecutionNotationFormula()),
                        Paragraph(Text(
                            "A live transition rejects an incoming seam 1 followed by a low "
                                + "bit 1. Otherwise it takes the high bit as the new seam and "
                                + "records whether the current window is nonzero as End. "
                            + "Legal(s,flatten(w)) includes the incoming seam and excludes "
                            + "adjacent ones in the complete flattened word."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("literal-window-legal-chain"),
                    DeclarationHandle.Create(Prefix + "legal_chain"),
                    H("Legal flattened words are window seam chains"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This interface exposes the adjacent-window chain form of the legal "
                        + "flattened language. FirstRejectionCutCapacity and the gap histogram "
                        + "module reuse it."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("literal-window-success-bijection"),
                    DeclarationHandle.Create(Prefix + "result"),
                    H("All successful bounded queries have an exact independent-set parametrization"),
                    StatementSource.FromAuthor(CountFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "All word lengths are numbers of whole windows. S_t is the set of "
                                + "words of length at most t with a true End flag after running "
                                + "from (seam,End)=(true,true); L_t contains every such literal "
                                + "word, and R_t contains those in L_t without success. I_t "
                                + "consists of independent Boolean selections at offsets "
                                + "1 through 3t-1, identified with their selected-position "
                                + "sets; I_0 is a singleton. The empty selection "
                                + "gives the empty query, which is charged and successful.")),
                        new DocumentBlock.DisplayFormula(WordFamiliesFormula()),
                        Paragraph(Text(
                            "Equiv(S_t,I_t) is the type of invertible maps; e inverse is the "
                                + "reverse map. Encode prepends "
                                + "the forced zero bit, packs windows, and removes only terminal "
                                + "whole 000 windows. Its inverse pads a successful word to t "
                                + "windows and flattens it. The selected offset below uses "
                                + "F_0=0 and F_1=1, so position 1 contributes v.")),
                        new DocumentBlock.DisplayFormula(OffsetFormula()),
                        Paragraph(Text(
                            "The modular value equality uses the same natural u and v after "
                                + "reduction modulo H. ZMod(H) is the residue ring and [a]_H "
                                + "denotes reduction of a natural a. CenterImage(t,H,u,v) is "
                                + "the set of negated modular values of successful words. A "
                                + "nonzero terminal window 100 or 010 is retained; first-01 "
                                + "words are retained. A trailing whole 000 window clears End "
                                + "and gives the same error for every numeric input.")),
                        new DocumentBlock.DisplayFormula(CenterImageFormula()),
                        Paragraph(Text(
                            "Initialized(epsilon,w) uses r=epsilon, u=2, v=3 and starts with "
                                + "both Boolean state fields equal to epsilon. Its successful "
                                + "numeric answer is positive. Applying the original terminal "
                                + "readout to that answer gives H divided by gcd(N,H).")),
                        Paragraph(Text(
                            "The existing admissible-word count gives F_(3t+1) successes. "
                                + "For t=3 there are 55 successes among 156 literal words, "
                                + "leaving 101 errors. The image of their modular translations "
                                + "or negated centers has at most 55 elements; different "
                                + "successful words may have the same modular image. "
                                + "This parametrization does not establish residue realization "
                                + "at a common returned row or the finite-center identification "
                                + "criterion.")),
                        new DocumentBlock.DisplayFormula(ThreeWindowFormula())),
                    DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Bool() => V("B");
    private static Formula Words() => Seq(V("W"), Caret, Grp(Star));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Sub(string name) => Seq(V(name), Underscore, Grp(V("t")));
    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Fib(Formula index) => Seq(V("F"), Underscore, Grp(index));
    private static Formula SumBound() => Seq(Sum, Underscore, Grp(V("n"), Eq, D(0)),
        Caret, Grp(V("t")), D(5), Caret, Grp(V("n")));
    private static Formula ZMod() => Call("ZMod", V("H"));
    private static Formula Some(Formula value) => Call("some", value);
    private static Formula State() => Some(Par(Seq(V("s"), Comma, Sp, V("E"))));
    private static Formula Run() => Call("run", State(), V("w"));
    private static Formula Legal() => Call("legal", V("s"), Call("flatten", V("w")));

    private static Formula ExecutionFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("s"), Comma, Sp, V("E"), Sp, InMacro, Sp, Bool(), Comma,
            Sp, Forall, Sp, V("w"), Sp, InMacro, Sp, Words(), Comma),
        Seq(Par(Seq(Run(), Sp, Eq, Sp, Some(Par(Seq(
                Call("lastFold", V("s"), V("w")), Comma, Sp,
                Call("endFold", V("E"), V("w"))))),
            Sp, Iff, Sp, Legal())), Sp, Land),
        Seq(Par(Seq(Run(), Sp, Eq, Sp, V("none"), Sp, Iff, Sp,
            Neg, Legal())), Dot),
    ]));

    private static Formula ExecutionNotationFormula() => Disp(new Formula.Aligned([
        Seq(Call("lastFold", V("s"), V("w")), Sp, Eq, Sp,
            Call("foldl", Par(Seq(Par(Seq(V("a"), Comma, Sp, V("b"))),
                Sp, Mapsto, Sp, Call("last", V("b")))), V("s"), V("w")), Comma),
        Seq(Call("endFold", V("E"), V("w")), Sp, Eq, Sp,
            Call("foldl", Par(Seq(Par(Seq(V("a"), Comma, Sp, V("b"))),
                Sp, Mapsto, Sp, Call("nonzero", V("b")))), V("E"), V("w")), Dot),
    ]));

    private static Formula WordFamiliesFormula() => Disp(new Formula.Aligned([
        Seq(Call("Success", V("w")), Sp, Iff, Sp,
            Call("endable", Call("run", Some(Par(Seq(V("true"), Comma, Sp,
                V("true")))), V("w"))), Sp, Eq, Sp, V("true"), Comma),
        Seq(Sub("S"), Sp, Eq, Sp, Seq(OpenBrace, V("w"), Sp, InMacro, Sp,
            Words(), Mid, Call("length", V("w")), Sp, Le, Sp, V("t"),
            Sp, Land, Sp, Call("Success", V("w")), CloseBrace), Comma),
        Seq(Sub("L"), Sp, Eq, Sp, Seq(OpenBrace, V("w"), Sp, InMacro, Sp,
            Words(), Mid, Call("length", V("w")), Sp, Le, Sp, V("t"),
            CloseBrace), Comma),
        Seq(Sub("R"), Sp, Eq, Sp, Seq(OpenBrace, V("w"), Sp, InMacro, Sp,
            Sub("L"), Mid, Neg, Call("Success", V("w")), CloseBrace), Comma),
        Seq(V("I"), Underscore, Grp(D(0)), Sp, Eq, Sp,
            OpenBrace, Emptyset, CloseBrace, Comma),
        Seq(V("t"), Sp, Gt, Sp, D(0), Sp, Implies, Sp,
            Sub("I"), Sp, Eq, Sp, OpenBrace, V("x"), Sp, Subseteq, Sp,
            OpenBrace, V("i"), Sp, InMacro, Sp, Nat(), Mid,
            D(1), Sp, Le, Sp, V("i"), Sp, Lt, Sp, D(3), V("t"), CloseBrace,
            Mid, Call("noAdjacent", V("x")), CloseBrace, Dot),
    ]));

    private static Formula OffsetFormula() => Disp(Seq(
        Call("O", V("t"), V("u"), V("v"), V("x")), Sp, Eq, Sp,
        Sum, Underscore, Grp(V("i"), Sp, InMacro, Sp, V("x")),
        Par(Seq(Fib(Seq(V("i"), Minus, D(1))), V("u"), Plus,
            Fib(V("i")), V("v"))), Comma,
        Sp, V("x"), Sp, InMacro, Sp, Sub("I"), Dot));

    private static Formula CenterImageFormula() => Disp(Seq(
        Call("centerImage", V("t"), V("H"), V("u"), V("v")), Sp, Eq, Sp,
        OpenBrace, Minus, Call("value", V("u"), V("v"), Call("flatten", V("w"))),
        Mid, Sp, V("w"), Sp, InMacro, Sp, Sub("S"), CloseBrace, Comma,
        Sp, V("u"), Comma, Sp, V("v"), Sp, InMacro, Sp, ZMod(), Dot));

    private static Formula E(Formula argument) => Seq(V("e"), Open, argument, Close);
    private static Formula Offset(Formula x) => Call("O", V("t"), V("u"), V("v"), x);
    private static Formula FibCount() => Fib(Seq(D(3), V("t"), Plus, D(1)));
    private static Formula Query() => Call("query", V("r"), V("u"), V("v"), V("w"));
    private static Formula AllQueryParameters(Formula body) =>
        All("w", Words(), All("r", Nat(), All("u", Nat(), All("v", Nat(), body))));
    private static Formula Reduced(string name) => Seq(OpenBracket, V(name), CloseBracket,
        Underscore, Grp(V("H")));

    private static Formula EncodeInverseClause() => All("x", Sub("I"), Seq(
        V("e"), Caret, Grp(Minus, D(1)), Open, V("x"), Close,
        Sp, Eq, Sp, Call("encode", V("t"), V("x"))));

    private static Formula PadInverseClause() => All("w", Sub("S"), Seq(
        Call("independentBits", V("t"), E(V("w"))), Sp, Eq, Sp,
        Call("flatten", Call("pad", V("t"), V("w")))));

    private static Formula NumericClause() => All("w", Sub("S"),
        All("r", Nat(), All("u", Nat(), All("v", Nat(), Seq(
            Query(), Sp, Eq, Sp, Some(Par(Seq(V("r"), Plus, Offset(E(V("w")))))))))));

    private static Formula ModularClause() => All("H", Nat(),
        All("u", Nat(), All("v", Nat(), All("w", Sub("S"), Seq(
            Call("value", Reduced("u"), Reduced("v"), Call("flatten", V("w"))),
            Sp, Eq, Sp, Seq(OpenBracket, Offset(E(V("w"))), CloseBracket,
                Underscore, Grp(V("H"))))))));

    private static Formula ErrorClause() => AllQueryParameters(Seq(
        Query(), Sp, Eq, Sp, V("none"), Sp, Iff, Sp,
        Neg, Call("Success", V("w"))));

    private static Formula PositiveClause() => AllQueryParameters(Seq(
        Par(Seq(Call("Success", V("w")), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, V("r"))), Sp, Implies, Sp,
        Par(Seq(Exists, Sp, V("N"), Sp, InMacro, Sp, Nat(), Comma, Sp,
            D(0), Sp, Lt, Sp, V("N"), Sp, Land, Sp,
            Query(), Sp, Eq, Sp, Some(V("N"))))));

    private static Formula ImageBoundClause() => All("H", Nat(),
        All("u", ZMod(), All("v", ZMod(), Seq(
            Card(Call("centerImage", V("t"), V("H"), V("u"), V("v"))),
            Sp, Le, Sp, FibCount()))));

    private static Formula InitializationClause() => All("epsilon", Bool(),
        All("w", Words(), All("N", Nat(), Seq(
            Call("initialized", V("epsilon"), V("w")), Sp, Eq, Sp,
            Some(V("N")), Sp, Implies, Sp, D(0), Sp, Lt, Sp, V("N")))));

    private static Formula Conjunct(Formula value) => Seq(Par(value), Sp, Land);

    private static Formula ThreeWindowFormula() => Disp(new Formula.Aligned([
        Seq(Card(Seq(V("S"), Underscore, Grp(D(3)))), Sp, Eq, Sp, D(5, 5), Comma,
            Sp, Card(Seq(V("L"), Underscore, Grp(D(3)))), Sp, Eq, Sp, D(1, 5, 6), Comma,
            Sp, Card(Seq(V("R"), Underscore, Grp(D(3)))), Sp, Eq, Sp, D(1, 0, 1), Comma),
        All("H", Nat(), All("u", ZMod(), All("v", ZMod(), Seq(
            Card(Call("centerImage", D(3), V("H"), V("u"), V("v"))),
            Sp, Le, Sp, D(5, 5), Dot)))),
    ]));

    private static Formula CountFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("t"), Sp, InMacro, Sp, Nat(), Comma,
            Sp, Open, Exists, Sp, V("e"), Colon, Sp,
            Call("Equiv", Sub("S"), Sub("I")), Comma),
        Conjunct(EncodeInverseClause()),
        Conjunct(PadInverseClause()),
        Conjunct(NumericClause()),
        Seq(Par(ModularClause()), Close, Sp, Land),
        Seq(Card(Sub("S")), Sp, Eq, Sp, FibCount(), Sp, Land),
        Conjunct(ErrorClause()),
        Conjunct(PositiveClause()),
        Seq(Card(Sub("L")), Sp, Eq, Sp, SumBound(), Sp, Land),
        Seq(Card(Sub("R")), Sp, Eq, Sp, SumBound(), Sp, Minus, Sp,
            FibCount(), Sp, Land),
        Conjunct(ImageBoundClause()),
        Seq(Par(InitializationClause()), Dot),
    ]));
}
