using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Rigidity;

internal sealed class NaturalSemiringRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every semiring automorphism of the natural numbers is the identity.",
        H("Natural Semiring Automorphism Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("natural-semiring-automorphism-is-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Rigidity/NaturalSemiringRigidity."
                    + "natural_semiring_automorphism_is_identity"),
                H("Every natural semiring automorphism is the identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("e"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("Aut")), Underscore, Grp(F.Id("sr")),
                    Open, Mathbb, Grp(F.Id("N")), Close, Comma, Sp,
                    F.Id("e"), Sp, Eq, Sp,
                    Mathrm, Grp(F.Id("id")), Underscore, Grp(Mathbb, Grp(F.Id("N")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A semiring automorphism of the natural numbers preserves every natural "
                        + "number because each natural is generated from zero and one by addition. "
                        + "Mathlib's map_natCast supplies this pointwise equality, and RingEquiv.ext "
                        + "promotes it to equality with the identity automorphism.")),
                    Paragraph(Text(
                        "This node formalizes only the claim in remark 27.15 that the additive "
                        + "structure collapses natural-number automorphisms to the identity. It does "
                        + "not formalize the atom's claims about Spec Z, program complexity, zeta, "
                        + "the Riemann hypothesis, or permutations in the multiplication-only "
                        + "structure."))),
                DescribeRole.Theorem))));
}
