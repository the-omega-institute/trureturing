using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class CubicEulerWilsonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/CubicEulerWilson.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The double cubic Euler sum is a central binomial coefficient; Wilson gives an explicit inverse-factorial cube in prime characteristic.",
        H("The Cubic Euler Sum and Wilson's Factorial Cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-wilson-inverse-factorial-cube"),
                DeclarationHandle.Create(Prefix + "neg_binomial_eq_inverse_factorial_cube"),
                H("Wilson gives an explicit cube"),
                StatementSource.FromAuthor(WilsonStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be any field of characteristic p, where p is prime, p = 3m + 1 and m is even. "
                        + "The negative central binomial coefficient choose(2m,m), cast into F, is the cube of the inverse of m!. "
                        + "The proof first works in ZMod p. The descending factorial from p-1 has value m! because m is even. "
                        + "Wilson's theorem therefore gives (2m)! m! = -1. The binomial factorial identity and "
                        + "the nonvanishing of m! then give -choose(2m,m)(m!)^3 = 1. Cancellation produces the displayed cube. "
                        + "The canonical prime-field homomorphism transports the identity to F, with no chosen field equivalence.")),
                    Paragraph(Text(
                        "This is a project derivation from the classical Wilson theorem and the factorial identities, with no novelty claim. "
                        + "The prime p determines the characteristic, rather than the cardinality of F. The theorem can therefore be used "
                        + "in extensions of the prime field, while the specific factorial index remains m = (p-1)/3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("double-cubic-euler-sum-binomial"),
                DeclarationHandle.Create(Prefix + "sum_double_cubic_euler"),
                H("Only one exponent survives the finite-field sum"),
                StatementSource.FromAuthor(EulerStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a finite field with card(F) = 3m + 1 and m even. Expand (1-x)^(2m) and sum over F. "
                        + "The exponents 2m+i range from 2m to 4m, so the only multiple of card(F)-1 = 3m is 3m, at i=m. "
                        + "The positive-exponent field power sum is -1 at that exponent and zero at the other exponents. "
                        + "The surviving sign (-1)^m equals one. Thus the sum is -choose(2m,m). "
                        + "The proof reuses Mathlib's unit-group power-sum formula and accounts for the zero field element explicitly.")),
                    Paragraph(Text(
                        "This coefficient extraction is derived here from the finite-field power-sum theorem; no literature novelty is asserted. "
                        + "It applies to finite fields of arbitrary prime-power degree subject to the explicit even-index premise, which forces odd cardinality. "
                        + "Combining it with the Wilson cube requires the separate equality card(F)=p. Without that extra hypothesis, "
                        + "the cardinality index in this theorem and the characteristic index in the preceding theorem can differ. "
                        + "For the cubic reciprocity continuation this supplies the double-exponent Euler reduction of the conjugate Jacobi sum "
                        + "in the original residue field. It proves the finite-field evaluation only; the character-conjugation and "
                        + "primary-generator bridges are supplied separately."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula ThreeMPlusOne() => F.Seq(D(3), F.Id("m"), Plus, D(1));
    private static Formula Choose() => Call("choose", F.Seq(D(2), F.Id("m")), F.Id("m"));
    private static Formula WilsonStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, Call("Field", F.Id("F")), Comma, Sp,
        Forall, Sp, F.Id("p"), Comma, Sp, Forall, Sp, F.Id("m"), Colon, Sp, F.Id("N"), Comma, Sp,
        Call("Prime", F.Id("p")), Comma, Sp, Call("CharP", F.Id("F"), F.Id("p")), Comma, Sp,
        F.Id("p"), Eq, ThreeMPlusOne(), Comma, Sp, Call("Even", F.Id("m")), Sp, Implies, Sp,
        Minus, Call("cast", Choose(), F.Id("F")), Eq,
        Call("pow", Call("inv", Call("cast", Call("factorial", F.Id("m")), F.Id("F"))), D(3))));
    private static Formula EulerStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, Call("FiniteField", F.Id("F")), Comma, Sp,
        Forall, Sp, F.Id("m"), Colon, Sp, F.Id("N"), Comma, Sp,
        Call("card", F.Id("F")), Eq, ThreeMPlusOne(), Comma, Sp,
        Call("Even", F.Id("m")), Sp, Implies, Sp,
        Sum, Underscore, Grp(F.Id("x"), InMacro, F.Id("F")), Sp,
        Call("pow", F.Id("x"), F.Seq(D(2), F.Id("m"))), Sp,
        Call("pow", F.Seq(D(1), Minus, F.Id("x")), F.Seq(D(2), F.Id("m"))), Eq,
        Minus, Call("cast", Choose(), F.Id("F"))));
}
