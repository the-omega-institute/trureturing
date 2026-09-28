using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class EisensteinPrimaryAssociateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/QuadraticIdeals/EisensteinPrimaryAssociate."
        + "exists_primary_associate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An Eisenstein integer whose norm is one modulo three has a primary associate.",
        H("Primary Associates in the Eisenstein Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("eisenstein-primary-associate"),
            DeclarationHandle.Create(Declaration),
            H("A norm-one unit makes the associate primary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be the integer quadratic algebra with omega squared plus omega "
                        + "plus one equal to zero. If the norm of z is one modulo three, "
                        + "there is a unit u of norm one such that 3 divides uz - 1. "
                        + "A norm-one element is a unit because its conjugate is an inverse.")),
                Paragraph(Text(
                    "Modulo three, the norm-one coordinate pairs are (1,0), (2,0), "
                        + "(0,1), (0,2), (1,1), and (2,2). Each is the residue of an "
                        + "Eisenstein unit, and multiplication by its inverse gives the "
                        + "primary associate. This supplies unit normalization after a "
                        + "prime generator is obtained; it does not construct that generator "
                        + "or factor the golden block."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("z");
        Formula u = F.Id("u");
        Formula order = F.Id("E");
        Formula normZ = Call("N", z);
        Formula normU = Call("N", u);
        Formula modThree = Seq(Open, Mathrm, Grp(F.Id("mod")), Sp, D(3), Close);
        Formula modThreeE = Seq(Open, Mathrm, Grp(F.Id("mod")), Sp, D(3), order, Close);

        return Disp(Seq(
            Forall, Sp, z, Sp, InMacro, Sp, order, Comma, Sp,
            normZ, Sp, Equiv, Sp, D(1), Sp, modThree, Sp, Rightarrow, Sp,
            Exists, Sp, u, Sp, InMacro, Sp, order, Comma, Sp,
            Call("IsUnit", u), Sp, Land, Sp,
            normU, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            u, z, Sp, Equiv, Sp, D(1), Sp, modThreeE, Dot));
    }
}
