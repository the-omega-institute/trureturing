using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FixedAlgebra;

internal sealed class RecordFixedAlgebraDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite record fixed algebra decomposes into its matrix blocks.",
        H("Record Fixed Algebra Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("record-fixed-algebra-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition."
                        + "record_fixed_algebra_decomposition"),
                H("The record fixed algebra is the product of its matrix blocks"),
                StatementSource.FromAuthor(RecordFixedAlgebraFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index type Lambda and finite address types I alpha, "
                            + "the block-diagonal embedding places one arbitrary complex "
                            + "matrix in each record class and realizes the fixed algebra as "
                            + "its range.")),
                    Paragraph(Text(
                        "The block-diagonal map is injective because extracting each diagonal "
                            + "block is a left inverse. Its range restriction is therefore a "
                            + "bijective algebra homomorphism, and Mathlib's AlgEquiv.ofBijective "
                            + "packages the resulting algebra isomorphism.")),
                    Paragraph(Text(
                        "Repository search found the finite-entry fixed-point characterization "
                            + "and the block-center result, but no general fixed-algebra "
                            + "decomposition. The source also explicitly records that this "
                            + "general finite-dimensional decomposition remains an open proof "
                            + "gap; the present statement supplies the block-diagonal algebra "
                            + "realization needed for the displayed decomposition."))),
                DescribeRole.Theorem))));

    private static Formula RecordFixedAlgebraFormula()
    {
        Formula index = Seq(F.Id("I"), Underscore, Grp(F.Id("alpha")));
        Formula matrix = Seq(
            Operatorname, Grp(F.Id("M")),
            Underscore, Grp(index),
            Open, Mathbb, Grp(F.Id("C")), Close, Close);
        Formula product = Seq(
            Open, F.Id("alpha"), Sp, Mapsto, Sp, matrix, Close);
        Formula fixedAlgebra = Seq(
            F.Id("recordFixedAlgebra"), Open, F.Id("I"), Close);

        return Disp(Seq(
            Forall, Sp, Lambda, Comma, Sp, F.Id("I"), Comma, Esc,
            OpenBracket, Forall, Sp, F.Id("alpha"), Comma, Sp,
            Operatorname, Grp(F.Id("Fintype")), Open,
            F.Id("I"), Underscore, Grp(F.Id("alpha")), Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Forall, Sp, F.Id("alpha"), Comma, Sp,
            Operatorname, Grp(F.Id("DecidableEq")), Open,
            F.Id("I"), Underscore, Grp(F.Id("alpha")), Close,
            CloseBracket, Comma, Esc,
            Operatorname, Grp(F.Id("AlgEquiv")), Open,
            fixedAlgebra, Comma, Sp, product, Close, Dot));
    }
}
