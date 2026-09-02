using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteSpectralLocalizerDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/FiniteSpectralLocalizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite non-Hermitian point gap admits a Hermitian chiral localizer.",
        H("Finite Spectral Localizer"),
        Blocks(
            Definition("position-shift", "positionShift",
                "Shifted position observable",
                "A finite position matrix is shifted by a real reference coordinate."),
            Definition("spectral-shift", "spectralShift",
                "Shifted spectral operator",
                "A finite operator is shifted by a complex reference point."),
            Definition("localizer", "finiteSpectralLocalizer",
                "Finite spectral localizer",
                "The shifted position and spectral operators form one doubled Hermitian block matrix."),
            Definition("grading", "chiralGrading",
                "Chiral grading",
                "The doubled carrier is graded by positive and negative identity blocks."),
            Definition("point-gap", "HasPointGap",
                "Finite point gap",
                "A point gap means that the shifted finite operator is a matrix unit."),
            Definition("hermitian-signature", "hermitianSignature",
                "Signed Hermitian inertia",
                "The signature reuses the repository positive and negative Hermitian indices."),
            Describe.Lean(
                DescribeId.Create("point-gap-localizer"),
                DeclarationHandle.Create(
                    Prefix + "has_point_gap_iff_zero_scale_localizer_isUnit"),
                H("Point gap equals zero-scale localizer invertibility"),
                StatementSource.FromAuthor(PointGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Real position shifts preserve Hermitianity, so a Hermitian position observable makes the complete block localizer Hermitian; at zero position scale only the spectral shift and its conjugate transpose remain, independently of the position input, and the square is the orthogonal block sum of the two spectral-shift Gram matrices.")),
                    Paragraph(Text(
                        "The chiral grading is involutive, anticommutes with the zero-scale localizer, negates it under conjugation, and pairs every nonzero eigenvector at an eigenvalue with one at its negative; Hermitian negation exchanges the strictly positive and strictly negative inertia counts, forcing the zero-scale inertia balance and the vanishing of the finite localizer signature.")),
                    Paragraph(Text(
                        "Over the complex numbers a finite point gap is exactly a nonzero shifted determinant, and it is equivalent to invertibility of the zero-scale chiral Hermitianization, of its determinant, of its square, and of both spectral-shift Gram blocks; conjugate transpose preserves the point-gap condition when the reference point is conjugated."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);


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

    private static Formula PointGapFormula() => Disp(Seq(
        Call("HasPointGap", F.Id("H"), F.Id("z")),
        Sp, Iff, Sp,
        Call("IsUnit",
            Call("finiteSpectralLocalizer",
                F.Id("X"), F.Id("H"), D(0), F.Id("x"), F.Id("z")))));
}
