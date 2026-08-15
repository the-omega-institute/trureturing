using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class FiniteTimeTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete finite-dimensional observation tower separates states within its rank budget.",
        H("Finite-Time Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-observation-towers-separate-in-finite-time"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/FiniteTimeTomography.finite_time_tomography"),
                H("A complete observation tower separates states within its rank budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("CompleteProgressiveTower")), Open,
                    Open, F.Id("V"), Underscore, F.Id("k"), Close,
                    Underscore, Grp(F.Id("k"), InMacro, Mathbb, Grp(F.Id("N"))), Close,
                    Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("m"), Leq,
                    Operatorname, Grp(F.Id("dim")), Open, F.Id("V"), Close, Minus,
                    Operatorname, Grp(F.Id("dim")), Open,
                    F.Id("V"), Underscore, D(0), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("q"), Underscore, F.Id("m"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V_k be an increasing tower of subspaces in a finite-dimensional "
                            + "space. Assume their supremum is the whole space and every proper "
                            + "stage grows strictly at the next step. Also assume that the "
                            + "accumulated readout q_k is injective whenever V_k is the whole "
                            + "space.")),
                    Paragraph(Text(
                        "Finite generation first gives some complete stage. Choose the earliest "
                            + "one. Every preceding inclusion is strict, so strict monotonicity "
                            + "of subspace dimension spends at least one rank at each step. The "
                            + "earliest complete stage is therefore at most dim V minus dim V_0, "
                            + "and its accumulated readout separates all states.")),
                    Paragraph(Text(
                        "LeanSearch found and the proof applies the exact mathlib chain theorem "
                            + "Submodule.FG.stabilizes_of_iSup_eq. Loogle supplied the exact "
                            + "finrank strict-monotonicity and maximal-rank lemmas; repository and "
                            + "formalization searches found no existing finite-time result."))),
                DescribeRole.Theorem))));
}
