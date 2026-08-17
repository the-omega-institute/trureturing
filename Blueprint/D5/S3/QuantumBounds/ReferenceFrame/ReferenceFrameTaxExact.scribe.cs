using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ReferenceFrameTaxExactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exchange model has an exact fidelity bridge, sharp tax, restricted flat tax, and paired top eigenspace.",
        H("Exact Finite Reference-Frame Tax"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-finite-reference-frame-tax-is-exact"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact"),
                H("The finite reference-frame tax is exact"),
                StatementSource.FromAuthor(ExactTaxFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The declaration packages the concrete exchange permutation, its "
                        + "conservation law, the finite Kraus representation, and both exact "
                        + "fidelity forms. It then applies the frozen sharp quadratic bound, "
                        + "the sine identity, the flat identity for ladders of length at least "
                        + "two, and the imported paired top-eigenspace characterization.")),
                    Paragraph(Text(
                        "The lower bound on the ladder length is explicit because the one-level "
                        + "flat calculation has tax one rather than the displayed three-halves "
                        + "formula."))),
                DescribeRole.Theorem))));

    private static Formula ExactTaxFormula() => F.Disp(F.Seq(
        F.Begin, F.Grp(F.Id("gathered")), F.Sp,
        F.Id("N"), F.Sp, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")),
        F.Comma, F.Quad, F.D(2), F.Leq, F.Sp, F.Id("N"),
        F.Longrightarrow, F.Sp, F.RowBreak, F.Sp,
        F.Id("U"), F.Underscore, F.Grp(F.Id("N")), F.Caret, F.Grp(F.Star),
        F.Sp, F.Id("U"), F.Underscore, F.Grp(F.Id("N")),
        F.Sp, F.Eq, F.Sp, F.Id("I"), F.Comma, F.Quad,
        F.Sp,
        F.Id("n"), F.Open, F.Id("exchange"), F.Open, F.Id("x"), F.Close,
        F.Close, F.Sp, F.Eq, F.Sp, F.Id("n"), F.Open, F.Id("x"), F.Close,
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Mathcal, F.Grp(F.Id("E")), F.Underscore, F.Grp(F.Id("c")),
        F.Open, F.Rho, F.Close, F.Sp, F.Eq, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("r"), F.Sp, F.InMacro, F.Sp,
            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close), F.Sp,
        F.Id("K"), F.Underscore, F.Grp(F.Id("r")), F.Sp, F.Rho, F.Sp,
        F.Id("K"), F.Underscore, F.Grp(F.Id("r")), F.Caret, F.Grp(F.Star),
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Open, F.Id("c"), F.Close,
        F.Sp, F.Eq, F.Sp,
        F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open, F.Id("c"), F.Close,
        F.Sp, F.Eq, F.Sp,
        F.Lvert, F.Sp, F.Id("J"), F.Id("c"), F.Rvert,
        F.Underscore, F.Grp(F.D(2)), F.Caret, F.Grp(F.D(2)),
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Caret,
        F.Grp(F.Mathrm, F.Grp(F.Id("opt"))), F.Open, F.Id("N"), F.Close,
        F.Colon, F.Eq, F.Max, F.Underscore, F.Grp(
            F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
            F.Id("c"), F.Underscore, F.Grp(F.Id("i")), F.Caret, F.Grp(F.D(2)),
            F.Eq, F.D(1)), F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Open, F.Id("c"), F.Close,
        F.Sp, F.Eq, F.Sp,
        F.Operatorname, F.Grp(F.Id("cos")), F.Open,
        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)), F.Close,
        F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.D(1), F.Minus,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Caret,
        F.Grp(F.Mathrm, F.Grp(F.Id("opt"))), F.Open, F.Id("N"), F.Close,
        F.Sp, F.Eq, F.Sp,
        F.Sin, F.Open,
        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)), F.Close,
        F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.D(2), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Longrightarrow, F.Sp,
        F.D(1), F.Minus,
        F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open,
        F.Open, F.Frac, F.Grp(F.D(1)), F.Grp(F.Sqrt, F.Grp(F.Id("N"))), F.Close,
        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close),
        F.Close, F.Sp, F.Eq, F.Sp,
        F.Frac, F.Grp(F.D(3)), F.Grp(F.D(2), F.Id("N")),
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Operatorname, F.Grp(F.Id("squaredTopEigenspace")),
        F.Open, F.Id("N"), F.Close, F.Sp, F.Eq, F.Sp,
        F.Operatorname, F.Grp(F.Id("topModeSpace")),
        F.Open, F.Id("N"), F.Close, F.Comma, F.Quad,
        F.Operatorname, F.Grp(F.Id("finrank")), F.Underscore,
        F.Grp(F.Mathbb, F.Grp(F.Id("R"))), F.Open,
        F.Operatorname, F.Grp(F.Id("squaredTopEigenspace")),
        F.Open, F.Id("N"), F.Close, F.Close,
        F.Sp, F.Eq, F.Sp, F.D(2),
        F.Sp, F.End, F.Grp(F.Id("gathered"))));
}
