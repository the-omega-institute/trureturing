using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CyclicTorsionFreeHomRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite cyclic group has no nonzero additive homomorphism to a torsion-free group.",
        H("Finite Cyclic Homomorphism Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-cyclic-hom-to-torsion-free-is-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/CyclicTorsionFreeHomRigidity."
                    + "zmod_hom_to_torsion_free_eq_zero"),
                H("Every map from a finite cyclic group to a torsion-free group is zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("n"), Sp, Neq, Sp, D(0), Comma, Sp,
                    Forall, Sp, F.Id("A"), Comma, Sp,
                    Mathrm, Grp(F.Id("IsAddTorsionFree")), Grp(F.Id("A")), Comma, Sp,
                    Forall, Sp, F.Id("f"), Sp, InMacro, Sp,
                    Mathrm, Grp(F.Id("Hom")),
                    Grp(Seq(Mathrm, Grp(F.Id("ZMod")), Grp(F.Id("n")), Comma, Sp, F.Id("A"))),
                    Comma, Sp, F.Id("f"), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n be nonzero and let A be a torsion-free additive commutative monoid. Every "
                        + "additive homomorphism f from ZMod n to A is the zero homomorphism. The source has "
                        + "characteristic n, so n times every source element is zero. Mapping this equality "
                        + "through f and using injectivity of multiplication by the nonzero integer n in A "
                        + "forces every value f(x) to be zero.")),
                    Paragraph(Text(
                        "The proof directly reuses mathlib's ZModModule.char_nsmul_eq_zero and "
                        + "nsmul_right_injective. Specializing n to 12 and A to the additive real numbers "
                        + "establishes Hom(Z/12Z, R) = 0, the torsion consequence used in appendix E.20. "
                        + "This node does not formalize the abelianization computation for PSL(2,Z), the "
                        + "bounded Euler-class defect formula, or the later quasimorphism classification."))),
                DescribeRole.Theorem))));
}
