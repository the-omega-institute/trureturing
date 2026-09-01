using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weyl displacement words compose with a phase fixed by the symplectic pairing.",
        H("Weyl Displacement Words over a Finite Cyclic Window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-displacement-word"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement"),
                H("The displacement word"),
                StatementSource.FromAuthor(DisplacementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displacement word at index (a, b) is the shift raised to the "
                            + "canonical natural representative of a, times the clock raised to "
                            + "the canonical natural representative of b. Both generators, their "
                            + "Weyl relation, their orders, and their unitarity are already frozen "
                            + "in the window register, which this module imports.")),
                    Paragraph(Text(
                        "The finite Weyl-Heisenberg group these words generate is classical, so "
                            + "no novelty is claimed for them. Appleby (2005), Journal of "
                            + "Mathematical Physics 46, 052107, doi 10.1063/1.1896384, defines the "
                            + "extended Clifford group as the normalizer of that group. Only the "
                            + "bibliographic identity and the published abstract were checked; the "
                            + "full text was not read, so the article is cited as background and "
                            + "not as the source of the identities proved below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul"),
                H("Composition law"),
                StatementSource.FromAuthor(DisplacementMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two displacement words multiply to a third, scaled by a single window "
                            + "phase. The exponent of that phase is the clock index of the left "
                            + "factor times the shift index of the right factor, and nothing "
                            + "else. The proof moves a clock power across a shift power by "
                            + "iterating the frozen Weyl relation twice, once in each exponent.")),
                    Paragraph(Text(
                        "Exponents are natural representatives of residues, so the identity needs "
                            + "the generators to see their exponents only modulo the window "
                            + "cardinality. That is supplied by the frozen order relations for the "
                            + "clock and the shift and by primitivity for the phase.")),
                    Paragraph(Text(
                        "The pinned Mathlib source carries no Weyl-Heisenberg material: no file "
                            + "mentions the Weyl-Heisenberg group, the generalized Pauli group, or "
                            + "clock and shift matrices, and no file is named after Pauli or "
                            + "Heisenberg. The displacement words are nevertheless classical, so "
                            + "the cited article records that no novelty is claimed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq"),
                H("Squaring identity"),
                StatementSource.FromAuthor(DisplacementSqFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Setting the two indices equal in the composition law gives the square of "
                            + "a displacement word as the doubled word carrying the phase whose "
                            + "exponent is the product of the two indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-two-not-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute"),
                H("The composition phase is not vacuous"),
                StatementSource.FromAuthor(DisplacementTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The composition law would read the same way if every phase were one, so "
                            + "a witness is recorded that the phase does real work. On the "
                            + "two-address window the words at (0, 1) and (1, 0) do not commute. "
                            + "Assuming they did forces the window phase to be its own square, "
                            + "hence one, contradicting primitivity."))),
                DescribeRole.Theorem))));

    private static Formula Displacement(Formula window, Formula first, Formula second) =>
        Call("displacement", window, first, second);

    private static Formula WindowContext(Formula window)
    {
        return Seq(
            Forall, Sp, window, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NeZero")), Open, window, Close,
            CloseBracket, Comma, Esc);
    }

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

    private static Formula DisplacementFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Displacement(m, a, b), Sp, Eq, Sp,
            Call("shiftMatrix", m), Caret, Grp(Call("val", a)), Sp, Cdot, Sp,
            Call("clockMatrix", m), Caret, Grp(Call("val", b)), Dot));
    }

    private static Formula DisplacementMulFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b, c, d),
            Displacement(m, a, b), Sp, Cdot, Sp, Displacement(m, c, d), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(b, Sp, Cdot, Sp, c))), Sp,
            Cdot, Sp,
            Displacement(m, Grp(a, Sp, Plus, Sp, c), Grp(b, Sp, Plus, Sp, d)), Dot));
    }

    private static Formula DisplacementSqFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            Displacement(m, a, b), Caret, Grp(Num(2)), Sp, Eq, Sp,
            Call("windowRoot", m), Caret, Grp(Call("val", Seq(a, Sp, Cdot, Sp, b))), Sp,
            Cdot, Sp,
            Displacement(m, Grp(a, Sp, Plus, Sp, a), Grp(b, Sp, Plus, Sp, b)), Dot));
    }

    private static Formula DisplacementTwoFormula()
    {
        Formula two = Num(2);
        Formula zero = Num(0);
        Formula one = Num(1);

        return Disp(Seq(
            Displacement(two, zero, one), Sp, Cdot, Sp, Displacement(two, one, zero), Sp,
            Neq, Sp,
            Displacement(two, one, zero), Sp, Cdot, Sp, Displacement(two, zero, one), Dot));
    }
}
