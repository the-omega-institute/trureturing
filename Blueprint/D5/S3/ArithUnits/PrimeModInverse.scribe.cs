using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class PrimeModInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A natural number not divisible by a prime is a unit modulo that prime.",
        H("Invertibility Modulo a Prime"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("not-divisible-by-a-prime-is-invertible-modulo-that-prime"),
                DeclarationHandle.Create("D5/S3/ArithUnits/PrimeModInverse.prime_not_dvd_is_unit"),
                H("Nondivisibility by a prime gives a unit modulo that prime"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("p"), Comma, F.Id("a"), InMacro,
                                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                                    F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Sp, Land, Sp,
                                    Neg, Open, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Close,
                                    Sp, Rightarrow, Sp,
                                    Operatorname, Grp(F.Id("IsUnit")), Open,
                                    OpenBracket, F.Id("a"), CloseBracket, Underscore, Grp(F.Id("p")),
                                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For every natural prime p and natural number a, if p does not divide "
                                        + "a, then the residue class of a in ZMod p is multiplicatively "
                                        + "invertible. This is the complete source clause: no converse, explicit "
                                        + "inverse construction, or unresolved subclaim is asserted.")),
                                    Paragraph(Text(
                                        "Repository searches found no declaration or Blueprint with this exact "
                                        + "adapter signature. The existing PrimeModUnit theorem characterizes "
                                        + "units modulo a prime as nonzero residues, while FermatLittle consumes "
                                        + "the same premise to prove a different modular-congruence conclusion.")),
                                    Paragraph(Text(
                                        "Pinned Mathlib supplies both bridge results needed here. "
                                        + "ZMod.isUnit_iff_coprime turns the goal into coprimality of a and p, "
                                        + "and Nat.Prime.coprime_iff_not_dvd converts the stated premise to "
                                        + "coprimality in the opposite order. Symmetry closes the adapter. The "
                                        + "nearby isUnit_prime_of_not_dvd reverses the mathematical roles by "
                                        + "making the prime the residue modulo an arbitrary modulus, so it is "
                                        + "not the target theorem. No inverse or coprimality argument is re-proved."))),
                DescribeRole.Theorem
            ))));
}
