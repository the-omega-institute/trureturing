using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class BlindKernelObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty blind residual obstructs every finite or pointwise language extension.",
        H("Blind Kernel Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blind-kernel-factorization-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction."
                        + "blind_kernel_obstruction"),
                H("Blind residuals obstruct every package extension"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The blind kernel is the intersection of the Setoid kernels of all "
                            + "definitions in the package. The blind residual intersects that "
                            + "kernel with the canonical defectRelation of the baseline readout "
                            + "and target; no second target-defect relation is introduced.")),
                    Paragraph(Text(
                        "If the residual is empty, adjoining the full pointwise language to the "
                            + "baseline eliminates the target defect. The remaining exhaustive "
                            + "alternative is either a sufficient finite selection or the stated "
                            + "compactification condition: full pointwise sufficiency with no "
                            + "finite sufficient selection.")),
                    Paragraph(Text(
                        "If the residual contains a pair, the baseline and every package "
                            + "definition agree on that pair while the target differs. Hence no "
                            + "finite indexed selection and no arbitrary subpackage pointwise "
                            + "union admits a target factor map. Repeated indices add no readout "
                            + "information, so arbitrary indexed unions are represented by their "
                            + "subpackage of values.")),
                    Paragraph(Text(
                        "The proof applies the accepted target recovery criterion to each "
                            + "persisting canonical defect. Thus the obstruction is inherited "
                            + "from the repository factorization theorem rather than reproved."))),
                DescribeRole.Theorem))));

    private static Formula Extension(Formula baseline, Formula definitions) =>
        Call("languageExtension", baseline, definitions);

    private static Formula Residual(Formula package, Formula baseline, Formula target) =>
        Call("blindResidual", package, baseline, target);

    private static Formula TheoremFormula()
    {
        Formula package = F.Id("Gamma");
        Formula baseline = F.Id("q");
        Formula target = F.Id("T");
        Formula definitions = F.Id("D");
        Formula subpackage = F.Id("Delta");
        Formula n = F.Id("n");
        Formula recover = F.Id("r");
        Formula residual = Residual(package, baseline, target);
        Formula finiteSelection =
            Call("finiteSelectionSufficient", package, baseline, target);
        Formula compactification =
            Call("compactificationRequired", package, baseline, target);
        Formula fullDefect =
            Call("defectRelation", Extension(baseline, package), target);
        Formula factorization(Formula family) =>
            Seq(Exists, Sp, recover, Comma, Sp, target, Sp, Eq, Sp,
                recover, Sp, Circ, Sp, Extension(baseline, family));
        Formula finiteObstruction = Seq(
            Forall, Sp, n, Comma, Sp, definitions, Colon, Sp,
            Call("Fin", n), Sp, To, Sp, package, Comma, Sp,
            Neg, Sp, Open, factorization(definitions), Close);
        Formula arbitraryObstruction = Seq(
            Forall, Sp, subpackage, Sp, Subseteq, Sp, package, Comma, Sp,
            Neg, Sp, Open, factorization(subpackage), Close);

        return Disp(Seq(
            Open, residual, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Open, fullDefect, Sp, Eq, Sp, Emptyset, Close, Sp, Land, Sp,
            Open, finiteSelection, Sp, Lor, Sp, compactification, Close, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Call("Nonempty", residual), Sp, Rightarrow, Sp,
            Open, finiteObstruction, Close, Sp, Land, RowBreak, Grp(),
            Open, arbitraryObstruction, Close, Sp, Land, Sp,
            Neg, finiteSelection, Close, Dot));
    }
}
