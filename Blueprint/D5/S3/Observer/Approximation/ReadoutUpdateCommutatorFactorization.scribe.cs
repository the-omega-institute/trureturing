using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Approximation;

internal sealed class ReadoutUpdateCommutatorFactorizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization."
            + "readout_update_commutator_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The readout-update commutator factors on its common domain and has the exact defect norm when bounded.",
        H("Readout-Update Commutator Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readout-update-commutator-factorization"),
                DeclarationHandle.Create(Declaration),
                H("The commutator factors and has the defect norm"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I be an address type, tau a reversible address permutation, and "
                            + "f a complex readout coefficient. The first conjunct identifies the "
                            + "independently constructed commutator with multiplication by the "
                            + "update defect after the update, on their natural common domain.")),
                    Paragraph(Text(
                        "For every proof that I is finite or f belongs to lp infinity, the second "
                            + "conjunct states that the norm of the bounded commutator is exactly "
                            + "the lp-infinity norm of the bundled update defect."))),
                DescribeRole.Theorem))));

    private static Formula FactorizationFormula()
    {
        Formula index = F.Id("I");
        Formula tau = F.Id("tau");
        Formula coefficient = F.Id("f");
        Formula boundedness = F.Id("h");

        Formula exactFactorization = Equal(
            Call("readoutUpdateCommutator", tau, coefficient),
            Call("factoredReadoutUpdateCommutator", tau, coefficient));
        Formula boundedPremise = Seq(
            Call("Finite", index), Sp, Lor, Sp,
            Call("MemLp", coefficient, Infty));
        Formula exactNorm = Equal(
            NormOf(Call("boundedReadoutUpdateCommutator", tau, coefficient, boundedness)),
            NormOf(Call("boundedReadoutDefect", tau, coefficient, boundedness)));

        return Disp(Seq(
            Forall, Sp, index, Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
            tau, Sp, Colon, Sp, Call("Perm", index), Comma, Sp,
            coefficient, Sp, Colon, Sp,
            index, Sp, To, Sp, Mathbb, Grp(F.Id("C")), Comma,
            RowBreak, Grp(),
            exactFactorization, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, boundedness, Sp, Colon, Sp, boundedPremise, Comma, Sp,
            exactNorm));
    }

    private static Formula NormOf(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

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
}
