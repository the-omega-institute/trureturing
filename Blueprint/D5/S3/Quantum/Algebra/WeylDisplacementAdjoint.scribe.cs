using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate-transposing a displacement word negates its index and costs one phase.",
        H("The Adjoint of a Weyl Displacement Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-shift-power-negated-inverse"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.shiftMatrix_pow_neg_mul"),
                H("A negated index inverts the shift power"),
                StatementSource.FromAuthor(ShiftNegFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two natural representatives sum to a multiple of the window "
                            + "cardinality, so the corresponding powers of the cyclic update "
                            + "annihilate to the identity by the frozen order relation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("weyl-shift-power-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.star_shiftMatrix_pow"),
                H("The adjoint of a shift power"),
                StatementSource.FromAuthor(StarShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The adjoint and the negated power are both left inverses of the same "
                            + "power. In a finite matrix algebra a one-sided inverse is two-sided, "
                            + "so the two agree. Unitarity of each power comes from the frozen "
                            + "unitarity of the generator by induction."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.displacement_adjoint"),
                H("Adjoint law"),
                StatementSource.FromAuthor(AdjointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Conjugate-transposing reverses the two factors and negates each index. "
                            + "Restoring the original order is one application of the frozen "
                            + "composition law, and it costs exactly the phase whose exponent is "
                            + "the product of the two original indices.")),
                    Paragraph(Text(
                        "The proof uses only the public composition law: the reversed product is "
                            + "the product of the words at (0, -b) and (-a, 0), so no separate "
                            + "commutation argument is needed."))),
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

    private static Formula ShiftNegFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a),
            Call("shiftMatrix", m), Caret, Grp(Call("val", Seq(Minus, a))), Sp, Cdot, Sp,
            Call("shiftMatrix", m), Caret, Grp(Call("val", a)), Sp, Eq, Sp, Num(1), Dot));
    }

    private static Formula StarShiftFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a),
            Call("star", Seq(Call("shiftMatrix", m), Caret, Grp(Call("val", a)))), Sp, Eq, Sp,
            Call("shiftMatrix", m), Caret, Grp(Call("val", Seq(Minus, a))), Dot));
    }

    private static Formula AdjointFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Call("star", Displacement(m, a, b)), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(a, Sp, Cdot, Sp, b))), Sp,
            Cdot, Sp,
            Displacement(m, Grp(Minus, a), Grp(Minus, b)), Dot));
    }
}
