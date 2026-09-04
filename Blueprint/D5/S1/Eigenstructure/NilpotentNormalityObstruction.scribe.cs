using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class NilpotentNormalityObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero nilpotent perturbation of a scalar cannot be normal or self-adjoint.",
        H("Nilpotent Normality Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-nilpotent-shift-not-normal"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/NilpotentNormalityObstruction."
                    + "nonzero_nilpotent_shift_not_normal"),
                H("A nonzero nilpotent scalar shift is not normal"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be a complex C-star algebra. If N is nonzero and nilpotent, "
                            + "then lambda times the identity plus N is not star-normal and "
                            + "therefore is not self-adjoint. Bounded operators for any chosen "
                            + "Hilbert-space inner product are a direct instance.")),
                    Paragraph(Text(
                        "The source headline mentions an operator having a nontrivial Jordan "
                            + "block, but its proof additionally assumes that the operator has "
                            + "the single-eigenvalue form lambda I plus nilpotent N. The formal "
                            + "statement records that necessary hypothesis explicitly instead "
                            + "of inferring a unique eigenvalue from the presence of one block.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no packaged theorem saying that a normal nilpotent "
                            + "element vanishes. The proof combines spectralRadius_pow_le with "
                            + "IsStarNormal.spectralRadius_eq_nnnorm, then uses "
                            + "Commute.isStarNormal_sub to remove the scalar part. The final "
                            + "self-adjoint obstruction uses IsSelfAdjoint.isStarNormal."))),
                DescribeRole.Theorem))));

    private static Formula ObstructionFormula()
    {
        Formula algebra = F.Id("A");
        Formula scalar = F.Id("lambda");
        Formula nilpotent = F.Id("N");
        Formula shifted = Seq(scalar, Sp, F.Id("I"), Sp, Plus, Sp, nilpotent);

        return Disp(Seq(
            Forall, Sp, algebra, Comma, Sp,
            Call("CStarAlgebra", algebra), Sp, Rightarrow, Esc,
            Forall, Sp, scalar, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("C")), Comma, Sp,
            nilpotent, Sp, InMacro, Sp, algebra, Comma, Esc,
            Open,
            Call("IsNilpotent", nilpotent), Sp, Land, Sp,
            nilpotent, Sp, Neq, Sp, D(0),
            Close, Sp, Rightarrow, Esc,
            Neg, Sp, Call("IsStarNormal", shifted), Sp, Land, Esc,
            Neg, Sp, Call("IsSelfAdjoint", shifted), Dot));
    }
}
