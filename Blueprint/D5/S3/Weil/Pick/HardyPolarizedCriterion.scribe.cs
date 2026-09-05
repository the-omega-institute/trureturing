using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class HardyPolarizedCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/HardyPolarizedCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Hardy Hankel block vanishes exactly when its negative-frequency coefficients vanish.",
        H("Hardy Polarized Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-hardy-hankel-block-vanishing-criterion"),
                DeclarationHandle.Create(Prefix + "hardy_polarized_criterion"),
                H("Finite Hardy Hankel block vanishing criterion"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite truncation, the Hankel block samples the coefficient "
                            + "sequence at i + j + 1, the negative-frequency tail of a Laurent "
                            + "symbol. Its vanishing is therefore equivalent to the vanishing "
                            + "of every sampled tail coefficient.")),
                    Paragraph(Text(
                        "This is the finite algebraic Hardy statement. The source-level "
                            + "identification of the symbol with a completed-zeta RH family is "
                            + "not assumed here, because that analytic bridge has no owner in "
                            + "the pinned library."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-coefficient-witness-for-nonzero-hankel-block"),
                DeclarationHandle.Create(Prefix + "hardy_nonzero_of_negative_coefficient"),
                H("A negative coefficient witnesses a nonzero Hankel block"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any explicitly nonzero sampled negative-frequency coefficient gives a "
                        + "matrix entry that is nonzero, hence constructs a concrete witness "
                        + "against Hankel-block vanishing."))),
                DescribeRole.Theorem))));

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

    private static Formula Coefficient() =>
        Seq(F.Id("c"), Underscore, Grp(Seq(F.Id("i"), Plus, F.Id("j"), Plus, D(1))));

    private static Formula Block() =>
        Call("H", F.Id("c"));

    private static Formula CriterionFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula index = Call("Fin", F.Id("n"));
        Formula condition = Seq(
            Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Sp, InMacro, Sp, index,
            Comma, Sp, Coefficient(), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            F.Id("c"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), F.Id("to"), complex,
            Comma, Sp, Block(), Sp, Eq, Sp, D(0), Sp,
            Iff, Sp, Grp(condition), Dot));
    }

    private static Formula WitnessFormula()
    {
        Formula index = Call("Fin", F.Id("n"));
        return Disp(Seq(
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            F.Id("c"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), F.Id("to"),
            Mathbb, Grp(F.Id("C")), Comma, Sp,
            Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Sp, InMacro, Sp, index,
            Comma, Sp, Coefficient(), Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Block(), Sp, Neq, Sp, D(0), Dot));
    }
}
