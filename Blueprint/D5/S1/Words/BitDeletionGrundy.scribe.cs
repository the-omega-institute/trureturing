using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class BitDeletionGrundyDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/BitDeletionGrundy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Define the OEIS A398916 bit-deletion game and prove both registered conjectures.",
        H("The Bit-Deletion Grundy Function"),
        Blocks(
            Paragraph(Text(
                "OEIS A398916 was contributed by Do Thanh Nhan on August 14, 2026, with "
                    + "the conjecture comments updated on August 20, 2026. The entry states "
                    + "both universal claims here only as conjectures. The entry proves the "
                    + "contextual formula a(2^n) = (n mod 2) + 1 and lists initial values, "
                    + "including a(37)=0; those facts are source context and are not restated "
                    + "here. The negative literature search is ASSUMED-UNVERIFIED for unindexed "
                    + "results.")),
            Definition(
                "mex", "minimum-excluded-value", "Minimum excluded value",
                MexDefinition(),
                AssessedProvenance.FromRepo(),
                "For a finite set S of natural numbers, mex uses a bounded scan from zero "
                    + "with card(S)+1 units of fuel. The pigeonhole bound guarantees that "
                    + "this executable scan reaches the mathematical minimum excluded value."),
            Theorem(
                "mex_spec", "minimum-excluded-specification", "The bounded scan is mex",
                MexSpecification(),
                AssessedProvenance.FromRepo(),
                "The returned value is absent from S and every smaller natural belongs to S."),
            Definition(
                "normalize", "leading-zero-normalization", "Leading-zero normalization",
                NormalizeDefinition(),
                AssessedProvenance.FromRepo(),
                "Normalization recursively removes leading zero bits, preserving an empty word "
                    + "and stopping at the first leading one."),
            Definition(
                "erasures", "positional-word-erasures", "Positional one-bit erasures",
                ErasuresDefinition(),
                AssessedProvenance.FromRepo(),
                "The erasure list contains the tail deletion first, followed by every recursive "
                    + "suffix deletion with the original head restored."),
            Definition(
                "wordGrundy", "word-grundy-recursion", "Bit deletion on binary words",
                WordGrundyDefinition(),
                AssessedProvenance.FromRepo(),
                "Words are MSB-first lists of bits. A leading zero is stripped. At a leading "
                    + "one, every positional one-bit deletion is normalized by stripping new "
                    + "leading zeros, duplicate results are identified as a finite set, and "
                    + "mex is applied. The empty word has value zero."),
            Definition(
                "transition0", "even-suffix-transition", "The even-suffix transition",
                Transition0Definition(),
                AssessedProvenance.FromRepo(),
                "T_0 sends state value 1 to 3 and every other value "
                    + "in Fin 4 to 1."),
            Definition(
                "transition1", "odd-suffix-transition", "The odd-suffix transition",
                Transition1Definition(),
                AssessedProvenance.FromRepo(),
                "T_1 sends state value 0 to 2 and every other value "
                    + "in Fin 4 to 0."),
            Definition(
                "parity", "word-length-parity", "Word-length parity",
                ParityDefinition(),
                AssessedProvenance.FromRepo(),
                "The empty word has even parity, and every cons toggles the suffix parity."),
            Definition(
                "transition", "parity-indexed-transition", "The parity-indexed transition",
                TransitionDefinition(),
                AssessedProvenance.FromRepo(),
                "False parity selects transition0 and true parity selects transition1."),
            Definition(
                "formula", "closed-form-automaton", "The closed-form automaton",
                FormulaDefinition(),
                AssessedProvenance.FromRepo(),
                "The formula reads an MSB-first word recursively from the right. A zero is "
                    + "ignored; a one applies T_0 when the remaining suffix has even length "
                    + "and T_1 when it has odd length. Here parity(w) is false for even "
                    + "length and true for odd length."),
            Theorem(
                "formula_append_zero_zero", "two-zero-formula-invariance",
                "Appending two zeros preserves the formula",
                FormulaAppendZeroZero(),
                AssessedProvenance.FromRepo(),
                "Two appended zero bits leave both the parity phase and the formula value "
                    + "unchanged."),
            Theorem(
                "wordGrundy_eq_formula", "automaton-mex-certificate",
                "The automaton computes the word game",
                WordGrundyEqualsFormula(),
                AssessedProvenance.FromRepo(),
                "The (p,h,M) automaton records suffix parity p, candidate value h, and the "
                    + "finite set M of deletion values. A table of 30 reachable states is "
                    + "closed under cons-0 and cons-1; kernel decide proves closure, state "
                    + "realization, and the cons-1 mex certificate. Strong induction on word "
                    + "length then identifies wordGrundy with val(formula). The injective "
                    + "four-bit code for M is only an implementation device for kernel "
                    + "reduction, not a change to the function computed by the automaton."),
            Definition(
                "bitDeletionSuccessors", "natural-bit-deletion-successors",
                "Natural successors by one binary-digit deletion",
                BitDeletionSuccessorsDefinition(),
                AssessedProvenance.FromRepo(),
                "For n in N, remove each positional digit from Mathlib's little-endian "
                    + "Nat.digits 2 n and re-encode the remaining list with Nat.ofDigits 2. "
                    + "The result is a Finset, so duplicate numerical outcomes are identified. "
                    + "Nat.ofDigits drops any high zero digits automatically, which agrees "
                    + "with leading-zero normalization. The word model corresponds to the "
                    + "natural-number recurrence under binary decoding."),
            Theorem(
                "bitDeletionSuccessors_lt", "natural-successors-are-smaller",
                "Every natural successor is smaller",
                BitDeletionSuccessorsLt(),
                AssessedProvenance.FromRepo(),
                "Deleting one digit shortens the canonical digit list by one. The "
                    + "ofDigits bound below two to the shortened binary length, together with "
                    + "the lower bound for the original canonical length, proves m<n. "
                    + "This is the well-foundedness side of that natural-number recurrence, to which this module's word model corresponds under binary decoding."),
            Definition(
                "g", "natural-bit-deletion-grundy", "The OEIS sequence function",
                GDefinition(),
                AssessedProvenance.FromRepo(),
                "Mathlib Nat.digits is little-endian. Reversal gives the canonical MSB-first "
                    + "binary expansion, and mapping a digit to the proposition d=1 gives its "
                    + "Boolean word. At n=0 this word is empty, hence g(0)=0."),
            Theorem(
                "g_mex_bitDeletionSuccessors", "natural-bit-deletion-mex-recurrence",
                "The natural-number mex recurrence",
                GMexBitDeletionSuccessors(),
                AssessedProvenance.FromRepo(),
                "The digit-decoding correspondence identifies every normalized word deletion "
                    + "with exactly one Nat.ofDigits successor, and identifies its wordGrundy "
                    + "value with g. Rewriting the word mex equation therefore gives the "
                    + "natural-number recurrence under binary decoding."),
            Theorem(
                "g_le_three", "grundy-values-at-most-three",
                "No Grundy value exceeds three",
                GBound(),
                AssessedProvenance.FromRepo(),
                "The automaton formula lies in Fin 4, so the word-game identification bounds "
                    + "every natural-number Grundy value by three."),
            Theorem(
                "g_four_mul", "fourfold-scaling-invariance",
                "Multiplication by four preserves the value",
                GFourMul(),
                AssessedProvenance.FromRepo(),
                "For nonzero n, Nat.digits_base_pow_mul identifies multiplication by four "
                    + "with appending the two bits 00 to the MSB-first word. The formula's "
                    + "two-zero invariance proves the claim; n=0 is immediate."),
            Theorem(
                "conjectures", "oeis-a398916-conjectures",
                "Both OEIS A398916 conjectures",
                Conjectures(),
                AssessedProvenance.FromRepo(),
                "Together these conclusions state that all values are at most three and "
                    + "g(4n)=g(n) for every natural n.")),
        []));

    private static DocumentBlock Definition(string declaration, string id, string title,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string declaration, string id, string title,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Separated(params Formula[] values)
    {
        var items = new List<Formula>();
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] values) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Separated(values)));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BoolWords() => Seq(F.Id("List"), Sp, F.Id("Bool"));
    private static Formula FinFour() => Seq(F.Id("Fin"), Sp, D(4));
    private static Formula FinsetNaturals() => Call("Finset", Naturals());
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Cons(byte bit, Formula word) => Call("cons", D(bit), word);
    private static Formula AppendedZeros(Formula word) =>
        Call("append", word, Seq(OpenBracket, D(0), Comma, Sp, D(0), CloseBracket));
    private static Formula FormulaValue(Formula word) => Call("formula", word);
    private static Formula WordValue(Formula word) => Call("wordGrundy", word);
    private static Formula Transition(byte parity, Formula value) =>
        Call($"transition{parity}", value);

    private static Formula MexDefinition()
    {
        Formula set = F.Id("S");
        return Disp(Seq(
            Bound("S", FinsetNaturals()),
            Call("mex", set), Sp, Eq, Sp,
            Call("mexScan", set, Seq(Call("card", set), Sp, Plus, Sp, D(1)), D(0))));
    }

    private static Formula MexSpecification()
    {
        Formula set = F.Id("S"), k = F.Id("k");
        Formula absent = Seq(Call("mex", set), Sp, Neg, InMacro, Sp, set);
        Formula minimal = Seq(
            Forall, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            k, Sp, Lt, Sp, Call("mex", set), Sp, Rightarrow, Sp,
            k, Sp, InMacro, Sp, set);
        return Disp(Seq(
            Bound("S", FinsetNaturals()),
            Parenthesized(absent), Sp, Land, Sp, Parenthesized(minimal)));
    }

    private static Formula NormalizeDefinition()
    {
        Formula w = F.Id("w");
        Formula emptyCase = Seq(Call("normalize", OpenBracketSequence()), Sp, Eq, Sp,
            OpenBracketSequence());
        Formula zeroCase = Seq(Bound("w", BoolWords()),
            Call("normalize", Cons(0, w)), Sp, Eq, Sp, Call("normalize", w));
        Formula oneCase = Seq(Bound("w", BoolWords()),
            Call("normalize", Cons(1, w)), Sp, Eq, Sp, Cons(1, w));
        return Disp(Seq(
            Parenthesized(emptyCase), Sp, Land, Sp,
            Parenthesized(zeroCase), Sp, Land, Sp,
            Parenthesized(oneCase)));
    }

    private static Formula ErasuresDefinition()
    {
        Formula alpha = Alpha, b = F.Id("b"), w = F.Id("w"), v = F.Id("v");
        Formula words = Call("List", alpha);
        Formula emptyCase = Seq(Call("erasures", OpenBracketSequence()), Sp, Eq, Sp,
            OpenBracketSequence());
        Formula restoredHead = Parenthesized(Seq(v, Sp, Mapsto, Sp, Call("cons", b, v)));
        Formula consCase = Seq(
            Bound("b", alpha),
            Bound("w", words),
            Call("erasures", Call("cons", b, w)), Sp, Eq, Sp,
            Call("cons", w, Call("map", restoredHead, Call("erasures", w))));
        return Disp(Seq(
            Forall, Sp, alpha, Colon, Sp, F.Id("Type"), Comma, Sp,
            Parenthesized(emptyCase), Sp, Land, Sp,
            Parenthesized(consCase)));
    }

    private static Formula WordGrundyDefinition()
    {
        Formula w = F.Id("w"), v = F.Id("v");
        Formula deletedValues = Seq(
            OpenBrace, WordValue(Call("normalize", v)), Sp, Mid, Sp,
            v, Sp, InMacro, Sp, Call("erasures", Cons(1, w)), CloseBrace);
        Formula emptyCase = Seq(WordValue(OpenBracketSequence()), Sp, Eq, Sp, D(0));
        Formula zeroCase = Seq(Bound("w", BoolWords()),
            WordValue(Cons(0, w)), Sp, Eq, Sp, WordValue(w));
        Formula oneCase = Seq(Bound("w", BoolWords()),
            WordValue(Cons(1, w)), Sp, Eq, Sp, Call("mex", deletedValues));
        return Disp(Seq(
            Parenthesized(emptyCase), Sp, Land, Sp,
            Parenthesized(zeroCase), Sp, Land, Sp,
            Parenthesized(oneCase)));
    }

    private static Formula Transition0Definition()
    {
        Formula h = F.Id("h");
        return Disp(Seq(
            Bound("h", FinFour()),
            Transition(0, h), Sp, Eq, Sp,
            Call("ite", Parenthesized(Seq(h, Sp, Eq, Sp, D(1))), D(3), D(1))));
    }

    private static Formula Transition1Definition()
    {
        Formula h = F.Id("h");
        return Disp(Seq(
            Bound("h", FinFour()),
            Transition(1, h), Sp, Eq, Sp,
            Call("ite", Parenthesized(Seq(h, Sp, Eq, Sp, D(0))), D(2), D(0))));
    }

    private static Formula ParityDefinition()
    {
        Formula b = F.Id("b"), w = F.Id("w");
        Formula emptyCase = Seq(Call("parity", OpenBracketSequence()), Sp, Eq, Sp, D(0));
        Formula consCase = Seq(
            Bound("b", F.Id("Bool")),
            Bound("w", BoolWords()),
            Call("parity", Call("cons", b, w)), Sp, Eq, Sp, Call("not", Call("parity", w)));
        return Disp(Seq(
            Parenthesized(emptyCase), Sp, Land, Sp,
            Parenthesized(consCase)));
    }

    private static Formula TransitionDefinition()
    {
        Formula h = F.Id("h");
        Formula evenCase = Seq(Bound("h", FinFour()),
            Call("transition", D(0), h), Sp, Eq, Sp, Transition(0, h));
        Formula oddCase = Seq(Bound("h", FinFour()),
            Call("transition", D(1), h), Sp, Eq, Sp, Transition(1, h));
        return Disp(Seq(
            Parenthesized(evenCase), Sp, Land, Sp,
            Parenthesized(oddCase)));
    }

    private static Formula FormulaDefinition()
    {
        Formula w = F.Id("w");
        Formula emptyCase = Seq(FormulaValue(OpenBracketSequence()), Sp, Eq, Sp, D(0));
        Formula zeroCase = Seq(Bound("w", BoolWords()),
            FormulaValue(Cons(0, w)), Sp, Eq, Sp, FormulaValue(w));
        Formula oneCase = Seq(Bound("w", BoolWords()),
            FormulaValue(Cons(1, w)), Sp, Eq, Sp,
            Call("transition", Call("parity", w), FormulaValue(w)));
        return Disp(Seq(
            Parenthesized(emptyCase), Sp, Land, Sp,
            Parenthesized(zeroCase), Sp, Land, Sp,
            Parenthesized(oneCase)));
    }

    private static Formula FormulaAppendZeroZero()
    {
        Formula w = F.Id("w");
        return Disp(Seq(
            Bound("w", BoolWords()),
            FormulaValue(AppendedZeros(w)), Sp, Eq, Sp, FormulaValue(w)));
    }

    private static Formula WordGrundyEqualsFormula()
    {
        Formula w = F.Id("w");
        return Disp(Seq(
            Bound("w", BoolWords()),
            WordValue(w), Sp, Eq, Sp, Call("val", FormulaValue(w))));
    }

    private static Formula BinaryWord(Formula n)
    {
        Formula d = F.Id("d");
        Formula predicate = Parenthesized(Seq(d, Sp, Eq, Sp, D(1)));
        return Call("map", Parenthesized(Seq(d, Sp, Mapsto, Sp, predicate)),
            Call("reverse", Call("digits", D(2), n)));
    }

    private static Formula GDefinition()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Bound("n", Naturals()),
            Call("g", n), Sp, Eq, Sp, WordValue(BinaryWord(n))));
    }


    private static Formula BitDeletionSuccessorsDefinition()
    {
        Formula n = F.Id("n");
        Formula digits = Call("digits", D(2), n);
        Formula erased = Call("erasures", digits);
        Formula carrier = Call("toFinset", erased);
        Formula image = Call("image", Call("ofDigits", D(2)), carrier);
        return Disp(Seq(
            Bound("n", Naturals()),
            Call("bitDeletionSuccessors", n), Sp, Eq, Sp, image));
    }

    private static Formula BitDeletionSuccessorsLt()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        Formula membership = Seq(
            m, Sp, InMacro, Sp, Call("bitDeletionSuccessors", n));
        return Disp(Seq(
            Bound("n", Naturals()),
            Bound("m", Naturals()),
            Parenthesized(membership), Sp, Rightarrow, Sp, m, Sp, Lt, Sp, n));
    }

    private static Formula GMexBitDeletionSuccessors()
    {
        Formula n = F.Id("n");
        Formula successors = Call("bitDeletionSuccessors", n);
        return Disp(Seq(
            Bound("n", Naturals()),
            Call("g", n), Sp, Eq, Sp,
            Call("mex", Call("image", F.Id("g"), successors))));
    }

    private static Formula GBound()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Bound("n", Naturals()),
            Call("g", n), Sp, Leq, Sp, D(3)));
    }

    private static Formula GFourMul()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Bound("n", Naturals()),
            Call("g", Seq(D(4), Sp, Cdot, Sp, n)), Sp, Eq, Sp, Call("g", n)));
    }

    private static Formula Conjectures()
    {
        Formula n = F.Id("n");
        Formula bound = Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Call("g", n), Sp, Leq, Sp, D(3));
        Formula scaling = Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Call("g", Seq(D(4), Sp, Cdot, Sp, n)), Sp, Eq, Sp, Call("g", n));
        return Disp(Seq(
            Parenthesized(bound), Sp, Land, Sp, Parenthesized(scaling)));
    }

    private static Formula OpenBracketSequence() => Seq(OpenBracket, CloseBracket);
}
