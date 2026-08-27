using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class KleeneStageLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An omega-continuous operator's least fixed point is the supremum of its finite stages.",
        H("Kleene Stage Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("least-fixed-point-is-the-supremum-of-finite-stages"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/KleeneStageLimit."
                    + "inductive_definition_is_supremum_of_stages"),
                H("The least fixed point is reached as a stage supremum"),
                StatementSource.FromAuthor(StageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be an omega-Scott-continuous order endomorphism of a complete "
                            + "lattice. Its least fixed point is the supremum of the finite "
                            + "iterates of f beginning at the bottom element.")),
                    Paragraph(Text(
                        "The Lean declaration is a thin repository wrapper around the exact "
                            + "pinned Mathlib theorem fixedPoints.lfp_eq_sSup_iterate. Repository "
                            + "searches found no equivalent D5 declaration; LeanSearch's API "
                            + "endpoint returned HTTP 404.")),
                    Paragraph(Text(
                        "This closes only the Kleene finite-stage clause of source theorem 7.6. "
                            + "It does not assert the atom's analytic-continuation analogy, "
                            + "independence claim, or free-choice interpretation."))),
                DescribeRole.Theorem))));

    private static Formula StageFormula()
    {
        Formula f = F.Id("f");
        Formula n = F.Id("n");
        Formula stage = Seq(
            f, Caret, Grp(OpenBracket, n, CloseBracket), Open,
            Operatorname, Grp(F.Id("bottom")), Close);
        Formula orderEndomorphism = Seq(
            Alpha, Sp, To, Underscore, Grp(F.Id("o")), Sp, Alpha);
        Formula omegaScottContinuous = Seq(
            Omega, Operatorname, Grp(F.Id("ScottContinuous")), Open, f, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Alpha, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("CompleteLattice", Alpha), CloseBracket, Comma, RowBreak, Grp(),
            f, Colon, Sp, orderEndomorphism, Comma, Sp,
            omegaScottContinuous, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("lfp")), Open, f, Close, Eq,
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(n, InMacro, Sp, Mathbb, Grp(F.Id("N"))), Sp, stage, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
