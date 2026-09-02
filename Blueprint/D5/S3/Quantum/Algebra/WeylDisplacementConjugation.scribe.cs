using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugating a displacement word by another rescales it by the symplectic phase.",
        H("Conjugation of Weyl Displacement Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-displacement-conjugation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementConjugation."
                        + "displacement_conjugation"),
                H("Conjugation law"),
                StatementSource.FromAuthor(ConjugationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Conjugating the displacement word D (c, d) by D (a, b) gives back "
                            + "D (c, d), scaled by a single root of unity whose exponent is the "
                            + "symplectic pairing b * c - a * d of the two index pairs.")),
                    Paragraph(Text(
                        "The proof composes two already-frozen laws of this family, the "
                            + "composition law and the adjoint law. The phase bookkeeping is "
                            + "redone locally because the corresponding helper in the frozen "
                            + "module is private and frozen modules are not amended.")),
                    Paragraph(Text(
                        "The exponent is antisymmetric under swapping the two index pairs, "
                            + "which can be read off the displayed statement. Nothing beyond "
                            + "that is claimed: this node asserts no criterion for when two "
                            + "words commute, and nothing about commutation subgroups, "
                            + "Clifford groups, or representation theory."))),
                DescribeRole.Theorem))));

    private static Formula Displacement(Formula window, Formula first, Formula second) =>
        Call("displacement", window, first, second);

    private static Formula WindowContext(Formula window) =>
        Seq(
            Forall, Sp, window, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NeZero")), Open, window, Close,
            CloseBracket, Comma, Esc);

    private static Formula Residues(Formula window, params Formula[] names)
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
        items.Add(window);
        items.Add(Close);
        items.Add(Comma);
        items.Add(Esc);
        return Seq([.. items]);
    }

    private static Formula ConjugationFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b, c, d),
            Displacement(m, a, b), Sp, Cdot, Sp, Displacement(m, c, d), Sp, Cdot, Sp,
            Call("star", Displacement(m, a, b)), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(
                b, Sp, Cdot, Sp, c, Sp, Minus, Sp, a, Sp, Cdot, Sp, d))), Sp,
            Cdot, Sp, Displacement(m, c, d), Dot));
    }
}
