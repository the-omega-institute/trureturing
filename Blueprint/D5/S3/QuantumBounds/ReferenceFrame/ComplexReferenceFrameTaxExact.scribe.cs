using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ComplexReferenceFrameTaxExactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exchange model has an exact complex-amplitude fidelity, tax, and paired top eigenspace.",
        H("Exact Complex Reference-Frame Tax"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-complex-reference-frame-tax-is-exact"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExact."
                        + "complex_reference_frame_tax_exact"),
                H("The complex reference-frame tax is exact"),
                StatementSource.FromAuthor(ExactComplexTaxFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For ladders of length at least two, the exchange permutation is unitary "
                            + "and conserves total excitation. For every complex reference vector, "
                            + "the channel entanglement fidelity is exactly the squared norm of "
                            + "zero-boundary nearest-neighbour averaging.")),
                    Paragraph(Text(
                        "The complex unit sphere has the same sharp cosine-squared optimum as the "
                            + "real sphere, so the complementary optimal tax is sine-squared. The "
                            + "normalized flat complex vector has tax three over two N.")),
                    Paragraph(Text(
                        "The squared complex path-average eigenspace at the sharp eigenvalue has "
                            + "complex dimension two. The lower bound on N is necessary because the "
                            + "one-level flat tax is one rather than three halves.")),
                    Paragraph(Text(
                        "Repository search found exact declarations for all four complex-amplitude "
                            + "clauses in the frozen complexification module; this declaration "
                            + "applies them directly and adds no replacement proof."))),
                DescribeRole.Theorem))));

    private static Formula ExactComplexTaxFormula() => F.Disp(F.Seq(
        F.Begin, F.Grp(F.Id("gathered")), F.Sp,
        F.Id("N"), F.Sp, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")),
        F.Comma, F.Quad, F.D(2), F.Leq, F.Sp, F.Id("N"),
        F.Longrightarrow, F.Sp, F.RowBreak, F.Sp,
        F.Id("U"), F.Underscore, F.Grp(F.Id("N")), F.Caret, F.Grp(F.Star),
        F.Sp, F.Id("U"), F.Underscore, F.Grp(F.Id("N")),
        F.Sp, F.Eq, F.Sp, F.Id("I"), F.Comma, F.Quad,
        F.Sp, F.Id("n"), F.Open, F.Id("exchange"), F.Open, F.Id("x"), F.Close,
        F.Close, F.Sp, F.Eq, F.Sp, F.Id("n"), F.Open, F.Id("x"), F.Close,
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Forall, F.Sp, F.Id("c"), F.Sp, F.InMacro, F.Sp,
        F.Mathbb, F.Grp(F.Id("C")), F.Caret, F.Grp(F.Id("N")),
        F.Comma, F.Quad, F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
        F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
        F.Lvert, F.Sp, F.Id("J"), F.Id("c"), F.Rvert,
        F.Underscore, F.Grp(F.D(2)), F.Caret, F.Grp(F.D(2)),
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Caret,
        F.Grp(F.Mathrm, F.Grp(F.Id("opt"))), F.Open, F.Id("N"), F.Close,
        F.Colon, F.Eq, F.Max, F.Underscore, F.Grp(
            F.Id("c"), F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("C")), F.Caret, F.Grp(F.Id("N")),
            F.Comma, F.Sp, F.Lvert, F.Sp, F.Id("c"), F.Rvert,
            F.Underscore, F.Grp(F.D(2)), F.Eq, F.D(1)), F.Sp,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
        F.Open, F.Id("c"), F.Close, F.Sp, F.Eq, F.Sp,
        F.Operatorname, F.Grp(F.Id("cos")), F.Open,
        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)), F.Close,
        F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.D(1), F.Minus,
        F.Id("F"), F.Underscore, F.Grp(F.Id("e")), F.Caret,
        F.Grp(F.Mathrm, F.Grp(F.Id("opt"))), F.Open, F.Id("N"), F.Close,
        F.Sp, F.Eq, F.Sp, F.Sin, F.Open,
        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)), F.Close,
        F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.D(1), F.Minus, F.Id("F"), F.Underscore, F.Grp(F.Id("e")),
        F.Open, F.Id("m"), F.Sp, F.Mapsto, F.Sp,
        F.D(1), F.Slash, F.Sqrt, F.Grp(F.Id("N")), F.Close,
        F.Sp, F.Eq, F.Sp, F.Frac, F.Grp(F.D(3)), F.Grp(F.D(2), F.Id("N")),
        F.Comma, F.Sp, F.RowBreak, F.Sp,
        F.Operatorname, F.Grp(F.Id("finrank")), F.Underscore,
        F.Grp(F.Mathbb, F.Grp(F.Id("C"))), F.Open,
        F.Operatorname, F.Grp(F.Id("eigenspace")), F.Open,
        F.Id("J"), F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp,
        F.Operatorname, F.Grp(F.Id("cos")), F.Open,
        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
        F.Close, F.Caret, F.Grp(F.D(2)), F.Close, F.Close,
        F.Sp, F.Eq, F.Sp, F.D(2),
        F.Sp, F.End, F.Grp(F.Id("gathered"))));
}
