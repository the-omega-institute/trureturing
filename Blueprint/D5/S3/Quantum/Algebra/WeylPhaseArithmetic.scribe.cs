using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylPhaseArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arithmetic of powers and products of the finite window root.",
        H("Arithmetic of the Weyl Window Root"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-phase-arithmetic-window-root-power-mod"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_mod"),
                H("Window-root powers depend only on the exponent modulo the window"),
                StatementSource.FromAuthor(WindowRootPowModFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The powers of the window root depend only on the exponent modulo M, "
                            + "because the root is a primitive M-th root of unity.")),
                    Paragraph(Text(
                        "The frozen WeylDisplacement module holds an equivalent of this first "
                            + "lemma behind private, so it cannot be imported, and frozen modules "
                            + "are not amended; this module is the single public home so that "
                            + "consumers import it rather than keeping a private copy each."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-phase-arithmetic-window-root-power-val-add"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_val_add"),
                H("Window-root phases multiply by adding their indices"),
                StatementSource.FromAuthor(WindowRootPowValAddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two phases multiply by adding their indices in ZMod M: the value of "
                            + "the sum is the exponent of the product of the two phases."))),
                DescribeRole.Theorem))));

    private static Formula WindowContext(Formula modulus) =>
        Seq(
            Forall, Sp, modulus, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NeZero")), Open, modulus, Close,
            CloseBracket, Comma, Esc);

    private static Formula NaturalExponent(Formula exponent) =>
        Seq(Forall, Sp, exponent, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc);

    private static Formula Residues(Formula modulus, params Formula[] names)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var index = 0; index < names.Length; index += 1)
        {
            items.Add(names[index]);
            if (index + 1 < names.Length)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
        }

        items.Add(Colon);
        items.Add(Sp);
        items.Add(Operatorname);
        items.Add(Grp(F.Id("ZMod")));
        items.Add(Open);
        items.Add(modulus);
        items.Add(Close);
        items.Add(Comma);
        items.Add(Esc);
        return Seq([.. items]);
    }

    private static Formula WindowRoot(Formula modulus) => Call("windowRoot", modulus);

    private static Formula WindowRootPowModFormula()
    {
        Formula modulus = F.Id("M");
        Formula exponent = F.Id("n");

        return Disp(Seq(
            WindowContext(modulus),
            NaturalExponent(exponent),
            WindowRoot(modulus), Caret, Grp(Call("mod", exponent, modulus)), Sp,
            Eq, Sp,
            WindowRoot(modulus), Caret, Grp(exponent), Dot));
    }

    private static Formula WindowRootPowValAddFormula()
    {
        Formula modulus = F.Id("M");
        Formula first = F.Id("x");
        Formula second = F.Id("y");

        return Disp(Seq(
            WindowContext(modulus),
            Residues(modulus, first, second),
            WindowRoot(modulus), Caret, Grp(Call("val", Seq(
                first, Sp, Plus, Sp, second))), Sp, Eq, Sp,
            WindowRoot(modulus), Caret, Grp(Call("val", first)), Sp,
            Cdot, Sp,
            WindowRoot(modulus), Caret, Grp(Call("val", second)), Dot));
    }
}
