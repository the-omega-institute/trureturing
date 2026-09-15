using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class ExactPrimeDivisionNoDFAODocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Automata/ExactPrimeDivisionNoDFAO.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime multiply-divide register defeats every finite-state automaton at each positive power.",
        H("Exact Prime Division Defeats Every Finite Automaton"),
        Blocks(
            Paragraph(Text(
                "Fix a prime p and an exponent a with a at least one. A register holds a natural "
                + "number, starts at one, and reads a word over two letters: true multiplies by "
                + "p, and false divides by p and is undefined unless p divides the current "
                + "value. A word is legal when every step is defined, and the reached values "
                + "along legal words are exactly the powers of p. The question asked of a "
                + "machine is a single bit: does the integer reached carry p to the power a as "
                + "a divisor. The theorem says no machine with finitely many states answers "
                + "that question correctly on every legal word. Both restrictions are used. At "
                + "a equal to zero the bit is constantly true and one state suffices, and on "
                + "positional numerals rather than multiply and divide histories a remainder "
                + "automaton modulo p to the power a decides the same divisibility.")),
            Describe.Lean(
                DescribeId.Create("exact-prime-division-defeats-finite-automata"),
                DeclarationHandle.Create(Prefix + "no_finite_dfao_for_exact_prime_division"),
                H("No finite automaton decides the threshold"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The register is presented by its two defining equations rather than by a "
                    + "name, so the statement quantifies over every partial automaton on the "
                    + "natural numbers that starts at one and steps by that guarded arithmetic. "
                    + "Correctness is written out: on every word whose run is defined and "
                    + "reaches n, the machine's output bit agrees with whether p to the power a "
                    + "divides n. Nothing is demanded on words the register cannot run. The "
                    + "content is the construction. For a machine with n states the proof "
                    + "exhibits n + 1 legal prefixes, the prefix of index i being a + i "
                    + "multiplications, together with, for each pair of distinct indices, a "
                    + "continuation of exactly the smaller index plus one divisions on which "
                    + "the demanded bit differs. That these prefixes are legal and separated "
                    + "rests on an image lemma: the register run started at p to the e is the "
                    + "image under k maps to p to the k of a counter run on the exponent, which "
                    + "is where primality enters through the exact-division guard. The frozen "
                    + "state lower bound takes such a family as a hypothesis and returns "
                    + "n + 1 at most the number of states, contradicting n."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula() => Disp(Universal("p", Naturals(),
        Universal("a", Naturals(),
            Seq(Call1("Prime", F.Id("p")), Sp, Land, Sp, Less(D(0), F.Id("a")), Sp,
                Implies, Sp,
                Forall, Sp, F.Id("register"), Sp, Colon, Sp,
                Call2("PartialDFA", Booleans(), Naturals()), Comma, Sp,
                Paren(Seq(
                    Equal(Call1("start", F.Id("register")), D(1)), Sp, Land, Sp,
                    Universal("n", Naturals(), Universal("u", Booleans(),
                        Equal(Call3("step", F.Id("register"), F.Id("n"), F.Id("u")),
                            StepValue()))))),
                Sp, Implies, Sp,
                Forall, Sp, F.Id("S"), Sp, InMacro, Sp, F.Id("Type"), Comma, Sp,
                Paren(Seq(Call1("Finite", F.Id("S")), Sp, Implies, Sp,
                    Forall, Sp, F.Id("M"), Sp, Colon, Sp,
                    Call3("DFAO", Booleans(), Booleans(), F.Id("S")), Comma, Sp,
                    Neg, Sp, Paren(Universal("w", Words(), Universal("n", Naturals(),
                        Seq(Equal(Call2("eval", F.Id("register"), F.Id("w")),
                                Call1("some", F.Id("n"))), Sp, Implies, Sp,
                            Paren(Seq(
                                Equal(Call2("evalOutput", F.Id("M"), F.Id("w")),
                                    F.Id("true")), Sp, Iff, Sp,
                                Seq(Pow(F.Id("p"), F.Id("a")), Sp, Mid, Sp,
                                    F.Id("n"))))))))))))));

    private static Formula StepValue() =>
        Seq(F.Id("if"), Sp, F.Id("u"), Sp, F.Id("then"), Sp,
            Call1("some", Mul(F.Id("n"), F.Id("p"))), Sp,
            F.Id("else"), Sp, F.Id("if"), Sp, F.Id("p"), Sp, Mid, Sp, F.Id("n"), Sp,
            F.Id("then"), Sp, Call1("some", Div(F.Id("n"), F.Id("p"))), Sp,
            F.Id("else"), Sp, F.Id("none"));

    private static Formula Naturals() => F.Id("Nat");

    private static Formula Booleans() => F.Id("Bool");

    private static Formula Words() => Call1("List", Booleans());

    private static Formula Paren(Formula a) => Seq(Left, Open, a, Right, Close);

    private static Formula Call1(string name, Formula a) =>
        Seq(F.Id(name), Left, Open, a, Right, Close);

    private static Formula Call2(string name, Formula a, Formula b) =>
        Seq(F.Id(name), Left, Open, a, Comma, Sp, b, Right, Close);

    private static Formula Call3(string name, Formula a, Formula b, Formula c) =>
        Seq(F.Id(name), Left, Open, a, Comma, Sp, b, Comma, Sp, c, Right, Close);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);

    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);

    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);

    private static Formula Div(Formula a, Formula b) => Seq(a, Sp, Slash, Sp, b);

    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
}
