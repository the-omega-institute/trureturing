using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralLeadingCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer leading matrices of the original elimination determinants",
        H("Four nonsingular integer matrices"),
        Blocks(
            Paragraph(Text("topR1 and topR2 are thirty by thirty integer matrices. topA and topC are twenty-eight by twenty-eight integer matrices. Their entries are fixed exactly by the integer arrays in the Lean definitions. LiteralSylvesterBounds identifies them with the weighted leading matrices of the original fixed resultants and linear minors, with every row and column in the source order.")),
            Paragraph(Text("Each matrix M has an explicit integer matrix T and an upper triangular integer matrix U. The entire entrywise identity T M=U is checked over the integers, together with upper triangularity and all nonzero diagonal entries of U. Determinant multiplicativity implies det(M) is nonzero. This argument makes no pivot choice and assumes no division or nonzero intermediate pivot.")),
            Describe.Lean(DescribeId.Create("literal-leading-determinants-nonzero"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralLeadingCertificates.leading_determinants_ne_zero"),
                H("The four integer determinants are nonzero"),
                StatementSource.FromAuthor(Nonzero()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The determinants of topR1, topR2, topA and topC are all nonzero integers. Their role is to establish exact polynomial degrees after the weighted leading-coefficient identities; they are not samples of an asserted resultant factorization."))), DescribeRole.Theorem)))));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);
    private static Formula Nonzero() => Disp(Seq(
        Call("det", Seq(F.Id("R"), Underscore, Grp(D(1)))), Neq, Sp, D(0), Land, Sp,
        Call("det", Seq(F.Id("R"), Underscore, Grp(D(2)))), Neq, Sp, D(0), Land, Sp,
        Call("det", F.Id("A")), Neq, Sp, D(0), Land, Sp,
        Call("det", F.Id("C")), Neq, Sp, D(0)));
}
