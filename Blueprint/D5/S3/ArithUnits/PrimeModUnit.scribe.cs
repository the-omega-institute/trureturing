using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class PrimeModUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An element modulo a prime is a unit exactly when it is nonzero.",
        H("Units Modulo a Prime"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-element-modulo-a-prime-is-a-unit-exactly-when-it-is-nonzero"),
                DeclarationHandle.Create("D5/S3/ArithUnits/PrimeModUnit.prime_modulus_is_unit_iff_ne_zero"),
                H("An element modulo a prime is a unit exactly when it is nonzero"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Comma, Quad,
                                    Forall, Sp, F.Id("a"), Sp, InMacro, Sp,
                                    Mathbb, Grp(F.Id("Z")), Slash, F.Id("p"), Mathbb, Grp(F.Id("Z")),
                                    Comma, Quad,
                                    Operatorname, Grp(F.Id("IsUnit")), Open, F.Id("a"), Close,
                                    Sp, Leftrightarrow, Sp, F.Id("a"), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For every natural prime p and every residue a modulo p, this theorem "
                                        + "identifies the multiplicatively invertible residues exactly with the "
                                        + "nonzero residues. Both directions are substantive: zero has no "
                                        + "multiplicative inverse, while primality ensures that every nonzero "
                                        + "residue has one.")),
                                    Paragraph(Text(
                                        "Mathlib already supplies the general equivalence isUnit_iff_ne_zero for "
                                        + "groups with zero and the field instance for ZMod p under a primality "
                                        + "Fact. The Lean proof only installs that Fact from the explicit "
                                        + "Nat.Prime hypothesis and applies the existing equivalence, so this is "
                                        + "a thin repository-addressed wrapper rather than a second proof."))),
                DescribeRole.Theorem
            ))));
}
