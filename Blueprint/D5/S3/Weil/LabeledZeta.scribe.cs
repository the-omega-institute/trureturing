using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class LabeledZetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/LabeledZeta",
            "A labeled Dirichlet vector remains nonzero at every spectral parameter."),
        H("Labeled Zeta Vectors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("labeled-zeta-vector-never-vanishes"),
                DeclarationHandle.Create("D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero"),
                H("The labeled vector never vanishes"),
                StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Operatorname, Grp(F.Id("labeledZeta")), Open, Ell, Comma, F.Id("s"), Close, Neq, Sp, D(0)))),
                AssessedProvenance.FromLiterature(
                                    LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert")),
                Blocks(Paragraph(Text(
                                    "The coordinate product needs no summability claim. Its empty-ledger coordinate is one, so the kernel-checked function cannot equal the zero vector."))),
                DescribeRole.Theorem
            ))));
}
