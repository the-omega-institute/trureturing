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
            + "inequality on every cutoff of the form 2^(6k).",
        H("Odious Majority on the Six-Bit Dyadic Slice"),
        Blocks(
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
                H("Odious integers dominate on every six-bit dyadic cutoff"),
                StatementSource.FromAuthor(NegativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Strong induction uses the three negative initial values and the positive "
                            + "recurrence coefficients 19, 209, and 189 to keep D_k strictly negative.")),
                    Paragraph(Text(
                        "A separate finite-sum induction identifies D_k with evilCount(k) minus "
                            + "odiousCount(k), so negativity gives the strict counting inequality.")),
                    Paragraph(Text(
                        "This proves only the infinite slice n=2^(6k). It does not claim the "
                            + "all-prefix Shevelev conjecture."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

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
                    Parenthesized(eligible), Sp, Iff, Sp, Parenthesized(residues))),
                Sp, Land, Sp),
            Seq(
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
            Seq(matrixIdentity, Sp, Land, Sp),
            Seq(
                Subscript(F.Id("D"), D(1)), Sp, Eq, Sp, Minus, D(6), Comma, Quad, Sp,
                Subscript(F.Id("D"), D(2)), Sp, Eq, Sp, Minus, D(4, 2), Comma, Quad, Sp,
                Subscript(F.Id("D"), D(3)), Sp, Eq, Sp, Minus, D(2, 0, 7, 0),
                Sp, Land, Sp),
            Seq(
                Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                k, Sp, Geq, Sp, D(1), Sp, Implies, Sp, recurrence, Dot),
        ]));
    }

    private static Formula NegativityFormula()
    {
        Formula k = F.Id("k");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                k, Sp, Geq, Sp, D(1), Comma),
            Seq(
                Subscript(F.Id("D"), k), Sp, Lt, Sp, D(0),
                Sp, Land, Sp,
                Call("evilCount", k), Sp, Lt, Sp, Call("odiousCount", k), Dot),
        ]));
    }
}
