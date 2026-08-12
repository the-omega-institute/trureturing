using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class FiniteReadoutKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A linear readout identifies its domain modulo its kernel with its attainable range.",
        H("Finite Readout Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-readout-is-its-kernel-quotient-projection"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteReadoutKernel.finite_readout_quotient_equiv_range"),
                H("A readout is its kernel-quotient projection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, F.Id("M"), Slash, Ker, Open, F.Id("readout"), Close, Close,
                    Sp, Equiv, Underscore, F.Id("R"), Sp,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("readout"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let R be a ring, let M and N be R-modules, and let readout be a "
                        + "linear map from M to N. Quotienting M by the kernel of readout "
                        + "identifies precisely the differences that no reading can detect. "
                        + "The resulting quotient is linearly equivalent to the range of "
                        + "readout, so it retains every attainable reading and no hidden "
                        + "kernel direction.")),
                    Paragraph(Text(
                        "The library was searched before proving. Pinned Mathlib already "
                        + "provides the exact first-isomorphism declaration as "
                        + "LinearMap.quotKerEquivRange, with its quotient representative and "
                        + "inverse image laws recorded by LinearMap.quotKerEquivRange_apply_mk "
                        + "and LinearMap.quotKerEquivRange_symm_apply_image. The Lean theorem "
                        + "is therefore a declared thin honest wrapper: it packages that "
                        + "equivalence as an inhabited proposition and introduces no parallel "
                        + "local proof. Repository searches found no prior D5 wrapper of the "
                        + "declaration or equivalent quotient-kernel statement.")),
                    Paragraph(Text(
                        "The source atom motivates the claim with a finite readout, but the "
                        + "first isomorphism theorem needs no finiteness assumption, so the "
                        + "formal statement is the honest module-theoretic generalization. It "
                        + "does not assert that readout is injective or surjective onto all of "
                        + "N, nor does it formalize a separate lattice-collision construction. "
                        + "The source atom contains no numerical certificate."))),
                DescribeRole.Theorem))));
}
