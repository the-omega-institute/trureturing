using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class HolomorphicCayleyHadamardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A paired rational complexification recovers the actual real squared-modulus residual and exposes its complex Jacobian.",
        H("Holomorphic Cayley Hadamard residuals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-cayleyphase"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.cayleyPhase"),
                H("cayleyPhase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex rational Cayley coordinate with a fixed phase prefactor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-pairedcayleyresidual"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyResidual"),
                H("pairedCayleyResidual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two analytic factors use fixed conjugated matrix coefficients and reciprocal phase companions. Complex normSq is not analytically continued."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-pairedcayleyjacobian"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyJacobian"),
                H("pairedCayleyJacobian"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rows are outcomes and columns are phase coordinates. The reciprocal factor contributes the negative second term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-paired-cayley-residual-hasfderivat"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_hasFDerivAt"),
                H("paired cayley residual hasFDerivAt"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete complex Frechet derivative is the continuous linear map represented by the displayed Jacobian. Both denominators must be nonzero; matrix H is fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-dephasedcayleyresidual"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephasedCayleyResidual"),
                H("dephasedCayleyResidual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix phase zero to one and omit outcome five, leaving a square five-variable system. The sixth residual remains minus the sum of the five retained residuals; a six-outcome sublevel additionally bounds that sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-dephased-cayley-residual-hasfderivat"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephased_cayley_residual_hasFDerivAt"),
                H("dephased cayley residual hasFDerivAt"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual five-by-five derivative is obtained by fixing coordinate zero and retaining the first five outcomes. No invertibility premise or conclusion is smuggled in."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-paired-cayley-residual-on-real"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_on_real"),
                H("paired cayley residual on real"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real phase coordinates the holomorphic paired residual equals the real norm-square measurement residual as a complex number. Arbitrary fixed complex chart phases are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holomorphiccayleyhadamard-paired-cayley-residual-sum-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_sum_zero"),
                H("paired cayley residual sum zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For scaled-unitary H and unit phase prefactors, the sum of all complex residuals is exactly zero throughout the pole-free domain. Matrix multiplication proves conservation without an identity-theorem oracle."))),
                DescribeRole.Theorem))));
}
