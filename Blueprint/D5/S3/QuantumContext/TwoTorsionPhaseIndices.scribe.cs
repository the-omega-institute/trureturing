using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class TwoTorsionPhaseIndicesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonzero indices killed by doubling modulo twenty-four are exactly three pairs.",
        H("Nonzero Two-Torsion Phase Indices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-two-torsion-phase-indices"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/TwoTorsionPhaseIndices."
                    + "nonzero_two_torsion_phase_indices"),
                H("The nonzero two-torsion indices form a three-point set"),
                StatementSource.FromAuthor(TwoTorsionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An index in the product of two residue groups modulo twenty-four is "
                            + "nonzero and killed by doubling exactly when it is one of (0,12), "
                            + "(12,0), or (12,12). Thus the nontrivial two-torsion subgroup has "
                            + "the three displayed phase indices.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies ZMod.neg_eq_self_iff, which classifies one "
                            + "coordinate fixed by negation, and ZMod.natCast_zmod_val, which "
                            + "identifies its nonzero residue as twelve. The Lean proof applies "
                            + "these results coordinatewise and excludes the zero pair.")),
                    Paragraph(Text(
                        "This closes only the two-torsion index classification in remark "
                            + "27.596, clause 3. It does not formalize the associated phase "
                            + "values, the claimed cross-tower isomorphism, or any exhaustive "
                            + "classification of the surrounding SIC data.")),
                    Paragraph(Text(
                        "Repository searches found no equivalent D5 declaration. The pinned "
                            + "Mathlib source search found the general one-coordinate theorem; "
                            + "local smart-search name queries found no full product theorem."))),
                DescribeRole.Theorem))));

    private static Formula TwoTorsionFormula()
    {
        Formula index = F.Id("q");
        Formula residuePair = Seq(
            Open, Mathbb, Grp(F.Id("Z")), Slash, D(2, 4), Mathbb, Grp(F.Id("Z")), Close,
            Caret, Grp(D(2)));
        Formula Pair(Formula first, Formula second) =>
            Seq(Open, first, Comma, Sp, second, Close);

        return Disp(Seq(
            Forall, Sp, index, InMacro, Sp, residuePair, Comma, Esc,
            Open, D(2), index, Eq, D(0), Sp, Land, Sp, index, Neq, D(0), Close,
            Sp, Leftrightarrow, Sp,
            index, Eq, Pair(D(0), D(1, 2)), Sp, Lor, Sp,
            index, Eq, Pair(D(1, 2), D(0)), Sp, Lor, Sp,
            index, Eq, Pair(D(1, 2), D(1, 2)), Dot));
    }
}
