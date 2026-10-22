using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFormalTwoSheetSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original formal two-sheet coordinate", H("Formal Two-Sheet Substitution"), Blocks(
            Paragraph(Text("The coefficient variable u is formal. T(u)=4u(1-u)^(-2) has zero constant term, "
                + "so substitution is the actual Mathlib power-series algebra homomorphism. "
                + "No evaluation at a complex number, analytic convergence, cutoff, or chosen square-root axiom is used.")),
            Describe.Lean(DescribeId.Create("formal-two-sheet-relation"),
                DeclarationHandle.Create(Prefix + "formal_two_sheet_relation"), H("Formal Coordinate Relation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("mul", Call("twoSheetSeries"),
                        Call("pow", Call("sub", F.D(1), F.Id("X")), F.D(2))),
                    Eq, Call("mul", F.D(4), F.Id("X"))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "T(u)(1-u)^2=4u is an identity in Complex formal power series. "
                    + "It is a normalization helper, not the missing charged-product theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-half-root-two-sheet"),
                DeclarationHandle.Create(Prefix + "original_half_root_two_sheet"), H("Original Half-Integer Root"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("sheetSubstitution", Call("halfRoot")), Eq,
                    Call("mul", Call("sub", F.D(1), F.Id("X")),
                        Call("inv", Call("add", F.D(1), F.Id("X"))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The unchanged binomial series with exponent -1/2, composed with T, equals (1-u)/(1+u). "
                    + "The proof uses its binomial square identity and formal substitution. "
                    + "Constant coefficient one excludes the other algebraic square-root branch. "
                    + "The complete original Lambda/J mode comparison and both charged all-j identities remain separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-half-integer-all-label-two-sheet"),
                DeclarationHandle.Create(Prefix + "original_half_integer_all_label_two_sheet"),
                H("Every Original Integer Label"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("E"), InMacro, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp,
                    Call("sheetSubstitution", Call("halfLabel", F.Id("E"))), Eq,
                    Call("twoSheetLabel", F.Id("E"))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For every integer E, the literal binomial series with coefficients choose(E/2,n), "
                    + "composed with T(u), equals (1+u)^E(1-u)^(-E). Integer induction treats positive "
                    + "and negative labels without a cutoff or a nonnegative-label premise. "
                    + "This supplies the exact scalar label substitution for the original local chart. "
                    + "It does not identify the full original Lambda/J normal operators or eliminate any retained variable."))),
                DescribeRole.Theorem))));
}
