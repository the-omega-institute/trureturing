using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class FiniteOccupationPartitionFunctionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite diagonal spectra admit exact fermionic and truncated bosonic occupation sums.",
        H("Finite Occupation Partition Functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fermionic-determinant-is-the-binary-occupation-sum"),
                DeclarationHandle.Create(Prefix + "fermionic_determinant_eq_occupation_sum"),
                H("The fermionic determinant is the binary occupation sum"),
                StatementSource.FromAuthor(FermionicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite diagonal spectrum e, the determinant of I plus x times "
                        + "diag(e) expands over functions from the mode set to Fin 2. Each "
                        + "spectral mode therefore occurs with exponent zero or one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bosonic-cutoff-has-an-exact-inverse-determinant-remainder"),
                DeclarationHandle.Create(
                    Prefix + "bosonic_trunc_eq_inverse_determinant_mul_remainder"),
                H("The bosonic cutoff has an exact inverse-determinant remainder"),
                StatementSource.FromAuthor(BosonicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Occupations through N form a finite product of geometric sums. "
                            + "Multiplication by det(I-x diag(e)) leaves exactly the product "
                            + "of the finite geometric remainders.")),
                    Paragraph(Text(
                        "The inverse-determinant form explicitly assumes every factor "
                            + "1-x e_i is nonzero. This excludes totalized division at zero.")),
                    Paragraph(Text(
                        "The source atom states an infinite Fredholm determinant and power "
                            + "series without a trace-class operator model or convergence "
                            + "hypotheses. The formal statement is the exact finite-spectrum, "
                            + "finite-cutoff specialization instead."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-mode-separates-fermionic-and-bosonic-occupations"),
                DeclarationHandle.Create(Prefix + "one_mode_fermionic_bosonic_witness"),
                H("One mode separates the two occupation rules"),
                StatementSource.FromAuthor(OneModeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At x=1 with one spectral value e=1, binary occupation contributes two "
                        + "states, while bosonic occupation zero, one, or two contributes "
                        + "three states. This is a concrete two-sided witness for the stated "
                        + "difference in state rules."))),
                DescribeRole.Theorem))));

    private static Formula FermionicFormula()
    {
        Formula k = F.Id("K"), d = F.Id("d"), x = F.Id("x"), e = F.Id("e");
        Formula i = F.Id("i"), occupation = F.Id("n");
        Formula finD = Seq(Operatorname, Grp(F.Id("Fin")), Open, d, Close);
        Formula finTwo = Seq(Operatorname, Grp(F.Id("Fin")), Open, D(2), Close);

        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, d, Comma, Sp, x, Comma, Sp, e, Comma, Esc,
            Operatorname, Grp(F.Id("det")), Open,
            F.Id("I"), Sp, Plus, Sp, x, Sp,
            Operatorname, Grp(F.Id("diag")), Open, e, Close, Close,
            Sp, Eq, Sp,
            Sum, Underscore, Grp(occupation, Colon, Sp, finD, Sp, To, Sp, finTwo), Sp,
            Prod, Underscore, Grp(i, Sp, InMacro, Sp, finD), Sp,
            Grp(x, e, Underscore, Grp(i)), Caret,
            Grp(occupation, Underscore, Grp(i)), Dot));
    }

    private static Formula BosonicFormula()
    {
        Formula k = F.Id("K"), d = F.Id("d"), n = F.Id("N");
        Formula x = F.Id("x"), e = F.Id("e"), i = F.Id("i");
        Formula finD = Seq(Operatorname, Grp(F.Id("Fin")), Open, d, Close);
        Formula denominator = Seq(D(1), Sp, Minus, Sp, x, e, Underscore, Grp(i));
        Formula nonzero = new Formula.Relation(
            denominator, FormulaRelationOperator.NotEqual, D(0));

        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, d, Comma, Sp, n, Comma, Sp, x, Comma, Sp, e,
            Comma, Esc,
            Open, Forall, Sp, i, Sp, InMacro, Sp, finD, Comma, Sp, nonzero, Close,
            Sp, Rightarrow, Sp,
            F.Id("Z"), Underscore, Grp(F.Id("B"), Comma, n), Open, x, Close,
            Sp, Eq, Sp,
            Frac,
            Grp(Prod, Underscore, Grp(i, Sp, InMacro, Sp, finD), Sp,
                Open, D(1), Minus,
                Grp(x, e, Underscore, Grp(i)), Caret, Grp(n, Plus, D(1)), Close),
            Grp(Operatorname, Grp(F.Id("det")), Open,
                F.Id("I"), Minus, x, Operatorname, Grp(F.Id("diag")), Open, e, Close, Close),
            Dot));
    }

    private static Formula OneModeFormula() => Disp(Seq(
        F.Id("Z"), Underscore, Grp(F.Id("F")), Caret, Grp(Open, D(1), Close),
        Open, D(1), Close, Sp, Eq, Sp, D(2), Sp, Land, Sp,
        F.Id("Z"), Underscore, Grp(F.Id("B"), Comma, D(2)),
        Caret, Grp(Open, D(1), Close), Open, D(1), Close, Sp, Eq, Sp, D(3), Dot));
}
