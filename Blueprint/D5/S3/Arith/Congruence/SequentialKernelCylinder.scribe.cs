using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SequentialKernelCylinderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "History-dependent Markov kernels multiply the caps of selected coordinate cylinders.",
        H("Selected Cylinders Under Sequential Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sequential-selected-cylinder-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/SequentialKernelCylinder.selected_cylinder_bound"),
                H("Only selected coordinates contribute a cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X(i) be measurable spaces. At time n, a Markov kernel "
                        + "kappa(n) samples X(n+1) from the entire history on indices "
                        + "0 through n. Every kernel is normalized at every history. "
                        + "Fix a <= b, a finite set S contained in the indices "
                        + "a+1 through b, measurable coordinate sets E(i), and "
                        + "extended nonnegative caps c(i). For every selected n+1 "
                        + "and every history z, assume kappa(n)(z)(E(n+1)) <= c(n+1).")),
                    Paragraph(Text(
                        "Under Mathlib's actual partial trajectory kernel, "
                        + "started at any fixed history through a, the integral "
                        + "of the product over i in S of the indicator of E(i) "
                        + "is at most the product over i in S of c(i). The "
                        + "product of indicators is the event that every "
                        + "selected coordinate lies in its specified set. "
                        + "The statement permits arbitrary measurable alphabets "
                        + "and therefore applies in particular to finite "
                        + "prime-power residue alphabets.")),
                    Paragraph(Text(
                        "The proof eliminates the last coordinate by induction "
                        + "on b. A selected last coordinate contributes its "
                        + "one-step conditional cap, and the tower identity "
                        + "reduces to the remaining selected set. An unselected "
                        + "last coordinate leaves the earlier observable "
                        + "unchanged by the existing Markov prefix theorem. "
                        + "Neither coordinate independence nor a joint "
                        + "cylinder bound is assumed.")),
                    Paragraph(Text(
                        "For the local-kernel covering argument, fix the "
                        + "head coordinates and choose S to be the earlier "
                        + "coordinates queried by a pair of actual residue "
                        + "classes. Each queried coordinate contributes one "
                        + "cylinder cap even when both classes query it. "
                        + "The further arithmetic second-moment expansion "
                        + "and the infinite prime-tail estimates are separate "
                        + "obligations."))),
                DescribeRole.Theorem))));
}
