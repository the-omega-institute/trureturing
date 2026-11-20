using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiTransverseCriticalPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed transverse phase over ZMod(p²) selects two stationary equations by exact upper-digit averaging.",
        H("The Pascadi Transverse Critical Phase"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-transverse-phase-variation"),
                DeclarationHandle.Create(Prefix + "phase_add_digits"),
                H("The two upper digits of the phase"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("Psi", F.Id("j"), F.Id("k")), Sp, Eq, Sp,
                    F.Id("Psi"), Grp(D(1), Plus, F.Id("p"),
                        Grp(F.Id("j"), F.Id("A"), Minus, F.Id("k"), F.Id("B")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Work over ZMod(p²). For d,n indexed by three coordinates, take l_i = λ − d_i − α n_i "
                    + "and Ψ = (l_1 l_2 l_3)/λ, with λ and all three factors units. Replacing λ and α by "
                    + "λ + pj and α + pk multiplies Ψ by 1 + p(jA − kB). Here A = sum_i 1/l_i − 1/λ "
                    + "and B = sum_i n_i/l_i. The construction expands the three factors and the unit inverse "
                    + "exactly using p² = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-transverse-signed-square"),
                DeclarationHandle.Create(Prefix + "signed_phase_sq"),
                H("The original signed reading has the prescribed square"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("Phi", F.Id("t")), Caret, D(2), Sp, Eq, Sp,
                    Frac, Grp(D(4), F.Id("Psi")), Grp(F.Id("g"), Call("s", F.Id("alpha")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Put u_i = l_3/l_i, S = sum_i u_i and s = s_0 + pα. Assume g s is a unit "
                    + "and λ sum_i 1/l_i = 1. If t² = S/(g s prod_i u_i), the signed reading "
                    + "Φ = t sum_i u_i(d_i + α n_i) squares to 4 Ψ/(g s). "
                    + "The proof uses sum_i u_i(d_i + α n_i) = −2l_3 and cancels the unit product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-transverse-unique-root"),
                DeclarationHandle.Create(Prefix + "existsUnique_radical_root_of_reduce"),
                H("The root above each nonzero residue is unique"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("UnitRoot", F.Id("r")), Sp, Implies, Sp,
                    Call("UniqueLift", F.Id("r"), F.Id("j"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an odd prime p, write R = 4 Ψ/(g s). A nonzero square root r of the reduction of R "
                    + "has a unique lift above r at every pair of upper digits j,k of λ,α on the unit chart. "
                    + "The proof corrects the square by the inverse of twice the root and uses p² = 0. "
                    + "Uniqueness follows because the sum of two roots above r is a unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-transverse-radical-orthogonality"),
                DeclarationHandle.Create(Prefix + "sum_radical_fibre"),
                H("Exact orthogonality on a signed root fibre"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("CharacterFibre", F.Id("z")), Sp, Eq, Sp,
                    Call("IfStationary", F.Seq(F.Id("p"), Caret, D(2)),
                        Call("e", F.Id("z")), D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be an odd prime and z be a unit square root of R in ZMod(p²). For every j,k "
                        + "in ZMod p, sum the prime-square additive character over roots above the residue of z "
                        + "of the radicand at λ + pj, α + pk. The resulting double sum equals p² e(z) when "
                        + "λ sum_i 1/l_i = 1 and sum_i n_i/l_i = 0 modulo p, and is zero otherwise.")),
                    Paragraph(Text(
                        "The root computation gives the exact lift z + p(z/2)(jA − kB). The two characters "
                        + "in j and k are independently orthogonal by Mathlib. The unit multiplier z/2 "
                        + "allows the vanishing of the character coefficients to recover both stationary equations. "
                        + "Cancellation between distinct stationary phases in the literal short box remains open."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
