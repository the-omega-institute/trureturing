using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class InertPrimeMod12Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inert prime factor of (6j)^2+1 is congruent to 5 modulo 12.",
        H("The Inert Bad-Prime Congruence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inert-prime-factor-of-thirtysix-jsq-plus-one-is-five-mod-twelve"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/InertPrimeMod12.inert_prime_dvd_mod_twelve"),
                H("An inert prime dividing (6j)^2+1 is 5 modulo 12"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), Sp, F.Id("p"), Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("p"), Sp, Mathrm, Grp(F.Id("prime")), Comma, Sp,
                    F.Id("p"), Sp, Mid, Sp, Open, D(6), F.Id("j"), Close, Caret, Grp(D(2)), Plus, D(1), Comma, Sp,
                    F.Id("p"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3), Sp, Eq, Sp, D(2), Sp,
                    Rightarrow, Sp,
                    F.Id("p"), Sp, Operatorname, Grp(F.Id("mod")), Sp, Num(12), Sp, Eq, Sp, D(5)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any prime p that is inert in the Eisenstein integers (p mod 3 = 2) and divides "
                        + "(6j)^2 + 1, the residue p mod 12 equals 5. A rational prime is inert in the Eisenstein "
                        + "integers exactly when p mod 3 = 2 (it splits when p mod 3 = 1 and ramifies at 3), so "
                        + "the hypothesis selects the inert factors; the split factors of (6j)^2 + 1 are instead "
                        + "congruent to 1 modulo 12, and are not constrained by this lemma.")),
                    Paragraph(Text(
                        "The proof is four steps. First p is not 2, since (6j)^2 + 1 is odd. Casting the "
                        + "divisibility p | (6j)^2 + 1 into ZMod p makes (6j)^2 = -1, so -1 is a square modulo p; "
                        + "the standard characterization of when -1 is a quadratic residue then forces p mod 4 to "
                        + "differ from 3, and with p odd this is p mod 4 = 1. Finally the two residues p mod 4 = 1 "
                        + "and p mod 3 = 2 combine, by the Chinese remainder theorem, to p mod 12 = 5.")),
                    Paragraph(Text(
                        "This records only the bad-prime lemma. Mathlib supplies the quadratic-residue "
                        + "characterization of -1 but no assembled inert bad-prime congruence. The statement does "
                        + "not cover the odd-core density theorem in which the lemma is used — the half-dimensional "
                        + "sieve estimate for the count of j whose value (6j)^2 + 1 is realized — which is far "
                        + "beyond this arithmetic congruence."))),
                DescribeRole.Theorem
            )),
        []));
}
