using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powers of a Weyl displacement word accumulate the triangular composition phase.",
        H("Powers of Weyl Displacement Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-displacement-power"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementPowers.displacement_pow"),
                H("Power law"),
                StatementSource.FromAuthor(DisplacementPowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The n-th power of a displacement word is the word at the n-fold "
                            + "index, scaled by one root of unity whose exponent is n.choose 2 "
                            + "times the product of the two indices.")),
                    Paragraph(Text(
                        "At step k, composition contributes k * a * b to the exponent. These "
                            + "contributions sum to the triangular number n.choose 2 times "
                            + "a * b. The proof is an induction on n resting on the frozen "
                            + "composition law.")),
                    Paragraph(Text(
                        "The frozen displacement_sq result is the n = 2 instance of this law. "
                            + "It remains exactly as frozen, and this module neither restates "
                            + "nor amends it."))),
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

    private static Formula DisplacementPowFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula n = F.Id("n");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Displacement(m, a, b), Caret, Grp(n), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(
                Call("choose", n, Num(2)), Sp, Cdot, Sp, a, Sp, Cdot, Sp, b))), Sp,
            Cdot, Sp,
            Displacement(
                m,
                Grp(n, Sp, Cdot, Sp, a),
                Grp(n, Sp, Cdot, Sp, b)),
            Dot));
    }
}
