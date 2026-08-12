using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class EigenframeInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A basis of eigenvectors has invariant coordinate lines.",
        H("Eigenframe Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eigenframe-coordinate-line-invariant"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/EigenframeInvariance."
                    + "eigenframe_coordinate_line_invariant"),
                H("Every coordinate line of an eigenframe is invariant"),
                StatementSource.FromAuthor(InvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be a linear endomorphism and b a basis indexed by i. "
                        + "When each b(i) is a nonzero eigenvector of f with eigenvalue "
                        + "lambda(i), the image under f of the scalar span of b(i) is "
                        + "contained in that same span for every index i.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No exact packaged "
                        + "eigenframe-invariance theorem was found. The proof is a thin "
                        + "wrapper over Module.End.HasEigenvector.apply_eq_smul, "
                        + "Submodule.map_le_iff_le_comap, and "
                        + "Submodule.span_singleton_le_iff_mem."))),
                DescribeRole.Theorem))));

    private static Formula InvarianceFormula()
    {
        Formula scalar = F.Id("R");
        Formula carrier = F.Id("M");
        Formula index = F.Id("I");
        Formula endomorphism = F.Id("f");
        Formula basis = F.Id("b");
        Formula eigenvalue = Lambda;
        Formula i = F.Id("i");
        Formula basisVector = Seq(basis, Open, i, Close);
        Formula indexedEigenvalue = Seq(eigenvalue, Open, i, Close);
        Formula scalarSpan = Seq(
            Operatorname, Grp(F.Id("span")), Underscore, Grp(scalar),
            OpenBrace, basisVector, CloseBrace);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, carrier, Comma, Sp, index, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CommRing")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("AddCommGroup")), Open, carrier, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Module")), Open, scalar, Comma, carrier, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp, endomorphism, InMacro,
            Operatorname, Grp(F.Id("End")), Underscore, Grp(scalar), Open, carrier, Close,
            Comma, Esc,
            Forall, Sp, basis, InMacro,
            Operatorname, Grp(F.Id("Basis")), Underscore, Grp(index),
            Open, scalar, Comma, carrier, Close, Comma, Esc,
            Forall, Sp, eigenvalue, Colon, index, To, Sp, scalar, Comma, Esc,
            Open, Forall, Sp, i, Comma, Esc,
            Operatorname, Grp(F.Id("HasEigenvector")),
            Open, endomorphism, Comma, indexedEigenvalue, Comma, basisVector, Close,
            Close, Sp, Rightarrow, Sp,
            Forall, Sp, i, Comma, Esc,
            Operatorname, Grp(F.Id("map")), Underscore, Grp(endomorphism),
            Open, scalarSpan, Close, Subseteq, scalarSpan, Dot));
    }
}
