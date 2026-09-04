using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementTwoTorsionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a two-torsion index, a displacement word and its overlap with a self-adjoint "
            + "matrix obey phase-weighted conjugation identities.",
        H("Two-Torsion Weyl Displacement Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-displacement-two-torsion-adjoint"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion."
                        + "star_displacement_of_two_torsion"),
                H("Adjoint at a two-torsion index"),
                StatementSource.FromAuthor(StarTwoTorsionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If both residue indices are two-torsion, each is equal to its own "
                            + "negative. Substituting these equalities into the displacement "
                            + "adjoint law leaves the original displacement word multiplied by "
                            + "the stated window phase."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-two-torsion-overlap-conjugate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion."
                        + "two_torsion_overlap_conj"),
                H("Conjugation of a two-torsion overlap"),
                StatementSource.FromAuthor(TwoTorsionOverlapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a self-adjoint matrix, conjugating the trace pairing reverses the "
                            + "product under the adjoint. The two-torsion adjoint identity and "
                            + "cyclicity of the trace then give the displayed phase times the "
                            + "original pairing.")),
                    Paragraph(Text(
                        "The result is only this conjugation identity. It makes no claim about "
                            + "density matrices, spectra, or geometric location."))),
                DescribeRole.Theorem))));

    private static Formula Displacement(Formula window, Formula first, Formula second) =>
        Call("displacement", window, first, second);

    private static Formula Trace(Formula matrix) => Call("trace", matrix);

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

    private static Formula MatrixType(Formula window) =>
        Call(
            "Matrix",
            Call("ZMod", window),
            Call("ZMod", window),
            Seq(Mathbb, Grp(F.Id("C"))));

    private static Formula TwoTorsionPremises(Formula first, Formula second)
    {
        Formula zero = Num(0);

        return Seq(
            Grp(first, Sp, Plus, Sp, first, Sp, Eq, Sp, zero), Sp, Implies, Sp,
            Grp(second, Sp, Plus, Sp, second, Sp, Eq, Sp, zero), Sp, Implies, Sp);
    }

    private static Formula Phase(Formula window, Formula first, Formula second) =>
        Seq(
            Call("windowRoot", window), Caret,
            Grp(Call("val", Seq(first, Sp, Cdot, Sp, second))));

    private static Formula StarTwoTorsionFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            TwoTorsionPremises(a, b),
            Call("star", Displacement(m, a, b)), Sp, Eq, Sp,
            Phase(m, a, b), Sp, Cdot, Sp, Displacement(m, a, b), Dot));
    }

    private static Formula TwoTorsionOverlapFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula rho = F.Id("rho");

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b),
            TwoTorsionPremises(a, b),
            Forall, Sp, rho, Colon, Sp, MatrixType(m), Comma, Esc,
            Grp(Call("star", rho), Sp, Eq, Sp, rho), Sp, Implies, Sp,
            Call("star", Trace(Seq(
                rho, Sp, Cdot, Sp, Displacement(m, a, b)))), Sp, Eq, Sp,
            Phase(m, a, b), Sp, Cdot, Sp,
            Trace(Seq(rho, Sp, Cdot, Sp, Displacement(m, a, b))), Dot));
    }
}
