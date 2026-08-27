using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PerfectEffectDiscriminationOrthogonalityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfect one-shot effect discrimination forces orthogonality.",
        H("Perfect Effect Discrimination Orthogonality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("perfect-effect-discrimination-orthogonal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality."
                        + "perfect_effect_discrimination_orthogonal"),
                H("Perfect effect discrimination forces orthogonality"),
                StatementSource.FromAuthor(DiscriminationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a finite complex matrix effect: both E and its complement "
                            + "are positive semidefinite. Let psi be normalized, suppose E "
                            + "accepts psi with probability one, and suppose E rejects phi "
                            + "with probability zero.")),
                    Paragraph(Text(
                        "A positive-semidefinite quadratic value vanishes exactly when the "
                            + "corresponding matrix kills the vector. Applied to the complement "
                            + "at psi and to E at phi, this gives E psi = psi and E phi = 0.")),
                    Paragraph(Text(
                        "Hermiticity of a positive-semidefinite matrix transfers E between the "
                            + "two slots of the overlap, so the overlap of phi with psi is zero. "
                            + "The theorem is stronger than the pure-state formulation because "
                            + "phi itself need not be normalized.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact discrimination "
                            + "theorem. The proof directly applies the pinned positive-matrix "
                            + "quadratic-zero criterion and standard matrix-vector identities."))),
                DescribeRole.Theorem))));

    private static Formula DiscriminationFormula()
    {
        Formula index = F.Id("I");
        Formula effect = F.Id("E");
        Formula psi = Psi;
        Formula phi = Phi;
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", index, index, complex);
        Formula vector = Seq(index, Sp, To, Sp, complex);
        Formula effectPsi = Call("mulVec", effect, psi);
        Formula effectPhi = Call("mulVec", effect, phi);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Fintype", index), Comma, Sp, Call("DecidableEq", index), Comma,
            RowBreak, Grp(),
            effect, Colon, Sp, matrix, Comma, Sp,
            psi, Comma, Sp, phi, Colon, Sp, vector, Comma,
            RowBreak, Grp(),
            Call("PosSemidefinite", effect), Sp, Land, Sp,
            Call("PosSemidefinite", Seq(D(1), Sp, Minus, Sp, effect)), Sp, Land,
            RowBreak, Grp(),
            Overlap(psi, psi), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Overlap(psi, effectPsi), Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            Overlap(phi, effectPhi), Sp, Eq, Sp, D(0), Sp, Rightarrow,
            RowBreak, Grp(),
            Overlap(phi, psi), Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Overlap(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

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
