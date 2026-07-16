using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class AlgebraicModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/AlgebraicModel",
            "The golden integer carrier is a quadratic quotient with explicit conjugation, trace, and norm."),
        H("Golden Algebraic Model"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("quadratic-quotient-conjugation-trace-and-norm"),
                DescribeKind.Definition,
                H("Quadratic quotient, conjugation, trace, and norm"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
                Blocks(Paragraph(Text(
                    "The coordinate ring is realized as the quotient at the golden polynomial. The kernel-checked conjunction identifies its distinguished root and gives the conjugate, trace, and norm formulas in integral coordinates.")))))));
}
