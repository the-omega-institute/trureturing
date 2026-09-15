using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class GuardedPrimeProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every divisor is a distinct predictive state for actual prime-product capacity checks.",
        H("The Minimal Guarded Prime-Product DFAO"),
        Blocks(
            Paragraph(Text(
                "Fix a positive natural N with at least one prime divisor. Inputs are the actual "
                + "prime divisors of N. A finite input word is evaluated as their integer product. "
                + "The requested Boolean output is whether that product divides N, so an exponent "
                + "overflow is rejected rather than silently clipped. These are multiplication "
                + "instructions, not binary or Zeckendorf digits of the final integer.")),
            Paragraph(Text(
                "Alphabet(N) is the subtype of Nat.primeFactors(N), Live(N) is the subtype of "
                + "Nat.divisors(N), value is the mapped List product, and target is the Boolean "
                + "divisibility test. The actual machine starts at the divisor 1. From d on "
                + "input p it moves to d*p if d*p divides N, otherwise to the absorbing state "
                + "none. Every live state outputs true and none outputs false.")),
            Describe.Lean(
                DescribeId.Create("guarded-prime-product-arithmetic-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/GuardedPrimeProduct.arithmetic_dfao_minimality"),
                H("Correctness and the exact total-state minimum"),
                StatementSource.FromAuthor(ArithmeticMinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public theorem states all-word correctness of the constructed "
                        + "DFAO, the cardinality of its explicit Option(Live(N)) state carrier, "
                        + "and the matching lower bound for every finite DFAO correct on the "
                        + "same entire prime-word domain. The supplied prime input witnesses "
                        + "the nonempty alphabet; N=1 is not incorrectly assigned a reachable "
                        + "reject state over an empty alphabet.")),
                    Paragraph(Text(
                        "Each divisor d has an actual prime-factor word. For live d and e, "
                        + "the continuation encoding N/d is accepted from e exactly when e "
                        + "divides d: cancel the positive common factor N/d. If d and e differ, "
                        + "one of the two complements separates them. The word encoding N "
                        + "followed by any alphabet prime reaches rejection, which differs "
                        + "from every live state already on the empty continuation. These "
                        + "witnesses instantiate the existing DFAOStateLowerBound owner.")),
                    Paragraph(Text(
                        "For N=5040 this yields 60 live states and one rejecting state, hence "
                        + "61 total states, all encodable in six bits. The theorem does not "
                        + "assert a universally optimal computer, a runtime bound, or that "
                        + "Zeckendorf storage creates the state lower bound. The 60-state "
                        + "partial machine and its 61-state totalization have different carriers."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Automata/DFAOStateLowerBound")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Alphabet() => Call("Alphabet", F.Id("N"));

    private static Formula Words() => Call("List", Alphabet());

    private static Formula Correct(Formula machine) => Seq(
        Open, Forall, Sp, F.Id("w"), Colon, Sp, Words(), Comma, Sp,
        Call("evalOutput", machine, F.Id("w")), Sp, Eq, Sp,
        Call("target", F.Id("N"), F.Id("w")), Close);

    private static Formula DivisorStateCount() => Seq(
        Call("card", Call("divisors", F.Id("N"))), Sp, Plus, Sp, D(1));

    private static Formula ArithmeticMinimalityFormula() => Disp(Seq(
        Forall, Sp, F.Id("N"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("hN"), Colon, Sp, F.Id("N"), Sp, Neq, Sp, D(0), Comma, Sp,
        Forall, Sp, F.Id("p"), Colon, Sp, Alphabet(), Comma, Sp,
        Correct(Call("machine", F.Id("hN"))), Sp, Land, Sp,
        Call("card", Call("Option", Call("Live", F.Id("N")))), Sp, Eq, Sp,
        DivisorStateCount(), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("S"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Call("Fintype", F.Id("S")), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("M"), Colon, Sp,
        Call("DFAO", Alphabet(), F.Id("Bool"), F.Id("S")), Comma, Sp,
        Correct(F.Id("M")), Sp, Rightarrow, Sp,
        DivisorStateCount(), Sp, Leq, Sp, Call("card", F.Id("S")), Close));
}
