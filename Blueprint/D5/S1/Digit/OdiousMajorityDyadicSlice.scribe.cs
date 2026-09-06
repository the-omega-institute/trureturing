using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class OdiousMajorityDyadicSliceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S1/Digit/OdiousMajorityDyadicSlice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact 21-state transfer certificate proves the Shevelev odious-majority "
            + "inequality on every cutoff 2^(6k) with k >= 1",
        H("Odious Majority on the Six-Bit Dyadic Slice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-index-type"),
                DeclarationHandle.Create(DeclarationPrefix + "Ix"),
                H("The residue index type"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Ix"), Sp, Eq, Sp, Call("Fin", D(2, 1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ix consists of the natural numbers from 0 through 20. Arithmetic in Ix "
                        + "is reduced modulo 21."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("standard-residue-basis"),
                DeclarationHandle.Create(DeclarationPrefix + "basis"),
                H("The standard residue columns"),
                StatementSource.FromAuthor(BasisFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The column e_j denotes basis(j); its coordinates are integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-transfer-matrix"),
                DeclarationHandle.Create(DeclarationPrefix + "T"),
                H("The signed binary transfer matrix"),
                StatementSource.FromAuthor(TransferDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "T is an integer matrix indexed by Ix in both coordinates. The conditions "
                        + "use arithmetic in Fin 21, including reduction of 2j and 2j+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("least-natural-residue"),
                DeclarationHandle.Create(DeclarationPrefix + "residue"),
                H("The least natural remainder"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    Call("val", Call("residue", F.Id("m"))), Sp, Eq, Sp,
                    new Formula.Modulo(F.Id("m"), D(2, 1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "residue(m) is the least natural remainder modulo 21, represented in Ix "
                        + "with the proof that it is less than 21."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-popcount"),
                DeclarationHandle.Create(DeclarationPrefix + "popcount"),
                H("The binary population count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    Call("popcount", F.Id("m")), Sp, Eq, Sp, BitCount(F.Id("m"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("popcount(m) counts the true entries of Nat.bits(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-residue-state"),
                DeclarationHandle.Create(DeclarationPrefix + "state"),
                H("The signed residue state"),
                StatementSource.FromAuthor(StateDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vector v_n denotes state(n). Here bits(m) is Nat.bits(m), and "
                        + "count(bits(m),true) is the number of true entries in that list. "
                        + "The integer sign multiplies the standard column at residue(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("eligible-selector-row"),
                DeclarationHandle.Create(DeclarationPrefix + "ell"),
                H("The eligible selector row"),
                StatementSource.FromAuthor(SelectorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integer row ell selects coordinates 7 and 14."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("six-bit-block-matrix"),
                DeclarationHandle.Create(DeclarationPrefix + "A"),
                H("The six-bit block matrix"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("A"), Sp, Eq, Sp, Power(F.Id("T"), D(6))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A is the sixth matrix power of T over the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-eligible-difference"),
                DeclarationHandle.Create(DeclarationPrefix + "D"),
                H("The signed eligible difference"),
                StatementSource.FromAuthor(DifferenceDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "D_k denotes D(k). The finite integer sum includes exactly natural "
                        + "numbers below 2^(6k) divisible by 7 and not by 3, with sign "
                        + "given by the count of true entries in Nat.bits(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odious-eligible-count"),
                DeclarationHandle.Create(DeclarationPrefix + "odiousCount"),
                H("The eligible odious count"),
                StatementSource.FromAuthor(CountDefinitionFormula("odiousCount", "Odd")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural cardinality counts the filtered Finset.range. Odd tests "
                        + "the number of true entries in Nat.bits(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("evil-eligible-count"),
                DeclarationHandle.Create(DeclarationPrefix + "evilCount"),
                H("The eligible evil count"),
                StatementSource.FromAuthor(CountDefinitionFormula("evilCount", "Even")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural cardinality counts the filtered Finset.range. Even tests "
                        + "the number of true entries in Nat.bits(m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-residue-transfer"),
                DeclarationHandle.Create(DeclarationPrefix + "state_eq_transfer_pow"),
                H("Signed residue counts obey the 21-state transfer"),
                StatementSource.FromAuthor(StateTransferFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state v_n records the signed popcount sum in each residue class "
                            + "modulo 21. Splitting the next binary range into even and odd "
                            + "integers transports the two residues to 2r and 2r+1 with opposite signs.")),
                    Paragraph(Text(
                        "The proof uses Nat.bit0_bits and Nat.bit1_bits on the live path, then "
                            + "iterates the one-bit equality from the standard vector e_0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eligible-residues-and-block-transfer"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "eligibility_iff_residue_and_D_eq_transfer"),
                H("Eligibility and the six-bit block coefficient agree exactly"),
                StatementSource.FromAuthor(EligibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Divisibility by 7 and nondivisibility by 3 select exactly residues 7 "
                            + "and 14 modulo 21. The selector row ell therefore turns the state "
                            + "at time 6k into the signed eligible difference D_k.")),
                    Paragraph(Text(
                        "The block matrix is A=T^6. This theorem packages both universal clauses "
                            + "of PZG candidate theorem 6.218 in one addressable declaration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("annihilator-and-third-order-recurrence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "annihilating_identity_and_D_recurrence"),
                H("The exact annihilator yields a third-order recurrence"),
                StatementSource.FromAuthor(AnnihilatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An ordinary kernel decision checks all 21 coordinates of the row "
                            + "certificate. Matrix algebra then gives the displayed annihilator "
                            + "and propagates it to every row after the first.")),
                    Paragraph(Text(
                        "The values D_1=-6 and D_2=-42 are decided directly over 64 and 4096 "
                            + "terms respectively; D_3=-2070 is decided through the matrix model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odious-majority-dyadic-negativity"),
                DeclarationHandle.Create(DeclarationPrefix + "D_negative"),
                H("Odious integers dominate for every k >= 1"),
                StatementSource.FromAuthor(NegativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The majority conjecture is Shevelev's (OEIS A229826; Int. J. Math. Math. Sci. "
                            + "2008). The dyadic-slice theorem and its transfer, certificate, and "
                            + "sign-induction proofs here are repository-derived.")),
                    Paragraph(Text(
                        "Strong induction uses the three negative initial values and the positive "
                            + "recurrence coefficients 19, 209, and 189 to keep D_k strictly negative.")),
                    Paragraph(Text(
                        "A separate finite-sum induction identifies D_k with evilCount(k) minus "
                            + "odiousCount(k), so negativity gives the strict counting inequality.")),
                    Paragraph(Text(
                        "This proves only the infinite slice n=2^(6k) with k >= 1. It does not claim the "
                            + "all-prefix Shevelev conjecture."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(F.Text, Grp(F.Id("if")), Sp, Parenthesized(condition), Sp,
            F.Text, Grp(F.Id("then")), Sp, yes, Sp, F.Text, Grp(F.Id("else")), Sp, no);

    private static Formula BitCount(Formula m) =>
        Call("count", Call("bits", m), Seq(Mathrm, Grp(F.Id("true"))));

    private static Formula SignValue(Formula m) =>
        Power(Parenthesized(Seq(Minus, D(1))), BitCount(m));

    private static Formula Eligible(Formula m) =>
        Parenthesized(Seq(D(7), Sp, Mid, Sp, m, Sp, Land, Sp,
            Neg, Sp, Parenthesized(Seq(D(3), Sp, Mid, Sp, m))));

    private static Formula Cutoff(Formula k) => Power(D(2), Seq(D(6), Sp, k));

    private static Formula BasisFormula()
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        return Disp(Seq(Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, F.Id("Ix"), Comma, Sp,
            Subscript(F.Id("e"), j), Parenthesized(i), Sp, Eq, Sp,
            Conditional(Seq(i, Sp, Eq, Sp, j), D(1), D(0))));
    }

    private static Formula TransferDefinitionFormula()
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, F.Id("Ix"), Comma),
            Seq(Subscript(F.Id("T"), Seq(i, j)), Sp, Eq, Sp,
                Parenthesized(Conditional(Seq(i, Sp, Eq, Sp, D(2), Sp, j), D(1), D(0))),
                Sp, Minus, Sp,
                Parenthesized(Conditional(Seq(i, Sp, Eq, Sp, D(2), Sp, j,
                    Sp, Plus, Sp, D(1)), D(1), D(0)))),
        ]));
    }

    private static Formula StateDefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Subscript(F.Id("v"), n), Sp, Eq, Sp,
            Subscript(Sum, Seq(m, Sp, InMacro, Sp, Call("range", Power(D(2), n)))), Sp,
            SignValue(m), Sp, Cdot, Sp, Subscript(F.Id("e"), Call("residue", m))));
    }

    private static Formula SelectorFormula()
    {
        Formula i = F.Id("i");
        return Disp(Seq(Forall, Sp, i, Sp, InMacro, Sp, F.Id("Ix"), Comma, Sp,
            Subscript(Ell, i), Sp, Eq, Sp,
            Conditional(Seq(i, Sp, Eq, Sp, D(7), Sp, Lor, Sp,
                i, Sp, Eq, Sp, D(1, 4)), D(1), D(0))));
    }

    private static Formula DifferenceDefinitionFormula()
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        return Disp(Seq(Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Subscript(F.Id("D"), k), Sp, Eq, Sp,
            Subscript(Sum, Seq(m, Sp, InMacro, Sp, Call("range", Cutoff(k)))), Sp,
            Parenthesized(Conditional(Eligible(m), SignValue(m), D(0)))));
    }

    private static Formula CountDefinitionFormula(string name, string parity)
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Call(name, k), Sp, Eq, Sp,
                Call("card", Call("filter", Call("range", Cutoff(k)),
                    Seq(m, Sp, Mapsto, Sp,
                        Parenthesized(Seq(Eligible(m), Sp, Land, Sp, Call(parity, BitCount(m)))))))),
        ]));
    }

    private static Formula StateTransferFormula()
    {
        Formula n = F.Id("n");
        Formula successor = Seq(n, Plus, D(1));
        Formula stateN = Subscript(F.Id("v"), n);
        Formula stateSucc = Subscript(F.Id("v"), successor);
        Formula basisZero = Subscript(F.Id("e"), D(0));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                stateSucc, Sp, Eq, Sp, F.Id("T"), Sp, stateN,
                Sp, Land, Sp,
                stateN, Sp, Eq, Sp, Power(F.Id("T"), n), Sp, basisZero, Dot),
        ]));
    }

    private static Formula EligibilityFormula()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula eligible = Seq(
            D(7), Sp, Mid, Sp, m, Sp, Land, Sp, Neg, Sp, D(3), Sp, Mid, Sp, m);
        Formula residues = Seq(
            Call("residue", m), Sp, Eq, Sp, D(7),
            Sp, Lor, Sp,
            Call("residue", m), Sp, Eq, Sp, D(1, 4));
        Formula blockCoefficient = Seq(
            Subscript(F.Id("D"), k), Sp, Eq, Sp,
            Ell, Sp, Cdot, Sp,
            Parenthesized(Seq(Power(F.Id("A"), k), Sp, Subscript(F.Id("e"), D(0)))));

        return Disp(new Formula.Aligned([
            Seq(
                Parenthesized(Seq(
                    Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    Parenthesized(eligible), Sp, Iff, Sp, Parenthesized(residues)))),
            Seq(
                Land, Sp,
                Parenthesized(Seq(
                    Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    blockCoefficient)), Dot),
        ]));
    }

    private static Formula AnnihilatorFormula()
    {
        Formula matrixIdentity = Seq(
            Ell, Sp, Cdot, Sp, F.Id("A"), Sp, Cdot, Sp,
            Parenthesized(Seq(
                Power(F.Id("A"), D(3)), Sp, Minus, Sp,
                D(1, 9), Sp, Power(F.Id("A"), D(2)), Sp, Minus, Sp,
                D(2, 0, 9), Sp, F.Id("A"), Sp, Minus, Sp,
                D(1, 8, 9), Sp, F.Id("I"))),
            Sp, Eq, Sp, D(0));
        Formula k = F.Id("k");
        Formula recurrence = Seq(
            Subscript(F.Id("D"), Seq(k, Plus, D(3))), Sp, Eq, Sp,
            D(1, 9), Sp, Subscript(F.Id("D"), Seq(k, Plus, D(2))), Sp, Plus, Sp,
            D(2, 0, 9), Sp, Subscript(F.Id("D"), Seq(k, Plus, D(1))), Sp, Plus, Sp,
            D(1, 8, 9), Sp, Subscript(F.Id("D"), k));

        return Disp(new Formula.Aligned([
            matrixIdentity,
            Seq(
                Land, Sp,
                Subscript(F.Id("D"), D(1)), Sp, Eq, Sp, Minus, D(6), Sp, Land, Sp,
                Subscript(F.Id("D"), D(2)), Sp, Eq, Sp, Minus, D(4, 2), Sp, Land, Sp,
                Subscript(F.Id("D"), D(3)), Sp, Eq, Sp, Minus, D(2, 0, 7, 0)),
            Seq(
                Land, Sp, Parenthesized(Seq(
                    Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    k, Sp, Geq, Sp, D(1), Sp, Implies, Sp, recurrence)), Dot),
        ]));
    }

    private static Formula NegativityFormula()
    {
        Formula k = F.Id("k");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                k, Sp, Geq, Sp, D(1), Sp, Implies, Sp,
                Parenthesized(Seq(
                    Subscript(F.Id("D"), k), Sp, Lt, Sp, D(0),
                    Sp, Land, Sp,
                    Call("evilCount", k), Sp, Lt, Sp, Call("odiousCount", k))), Dot),
        ]));
    }
}
