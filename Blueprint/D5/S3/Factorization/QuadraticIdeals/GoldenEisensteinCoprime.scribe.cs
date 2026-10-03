using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenEisensteinCoprimeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/QuadraticIdeals/GoldenEisensteinCoprime."
        + "golden_eisenstein_conjugate_coprime";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The oriented Eisenstein factor of each cubic Lucas block is coprime to its conjugate.",
        H("Coprime Conjugate Factors of Cubic Lucas Blocks"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-eisenstein-conjugate-coprime"),
            DeclarationHandle.Create(Declaration),
            H("The oriented factor and its conjugate generate the unit ideal"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For j at least one, let x be the Lucas number at index 3^j and let "
                        + "eta = -2 + (x - 1) omega in the Eisenstein order, where "
                        + "omega squared plus omega plus one is zero. The principal ideals "
                        + "of eta and its conjugate generate the unit ideal.")),
                Paragraph(Text(
                    "The Lucas residue x = 4 modulo 72 gives x = 4 + 72k for an integer k. "
                        + "The norm of eta is x squared plus three, while eta plus its "
                        + "conjugate equals -(x + 3). Since x squared plus three equals "
                        + "(x + 3)(x - 3) + 12 and x + 3 = 7 + 72k, explicit Bezout "
                        + "coefficients make these two integers coprime. Their image in "
                        + "the Eisenstein order supplies a Bezout identity for eta and "
                        + "its conjugate."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula j = F.Id("j");
        Formula eta = Seq(Langle, Minus, D(2), Comma, Sp,
            Call("goldenLucas", Seq(D(3), Caret, Grp(j))), Minus, D(1), Rangle);
        Formula conclusion = Call("IsCoprime", Call("IdealSpan", eta),
            Call("IdealSpan", Call("star", eta)));

        return Disp(Seq(Forall, Sp, j, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, j, Sp, Implies, Sp, conclusion, Dot));
    }
}
