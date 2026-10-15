using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeEnergyBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native tensor coordinates characterize every finite superposition in the zero-charge zero-energy sector.",
        H("Complete Exceptional Tensor Sector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-zero-sector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.mem_sector_iff"),
                H("Original total zero mode and fixed charge"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, Sp, F.Id("H"), Comma, Sp, F.Id("v"), Comma, Sp,
                    F.Id("H"), Times, Sp, Call("gramComplex", F.Id("D")), Sp, Eq, Sp, Num(1), Sp, Land, Sp,
                    Call("gramComplex", F.Id("D")), Times, Sp, F.Id("H"), Sp, Eq, Sp, Num(1), Sp, Rightarrow, Sp,
                    F.Id("v"), Sp, InMacro, Sp, Call("sector", F.Id("D")), Sp, Iff, Sp,
                    Call("chargeSupportZero", F.Id("v")), Sp, Land, Sp,
                    Call("TotalZeroMode", F.Id("v")), Sp, Eq, Sp, Num(0)))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The full matter basis is indexed by every integral charge and every finite oscillator exponent. Tensoring it with the complete exterior ghost basis gives coordinates for the unrestricted actual carrier. Both inverse-Gram equations identify the original matter zero mode with oscillator frequency plus half the lattice norm; the original ghost zero stress is diagonal with the native signed site energy.")),
                Paragraph(Text("Membership is equivalent to having no nonzero-charge coefficient and being killed by the original total zero mode. This equivalence holds for every finite superposition, not just for isolated tensor monomials. No null direction, adapted partner, frame, division by a charge pairing, or signature condition occurs.")))),
            Describe.Lean(
                DescribeId.Create("complete-exceptional-basis-dimension"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis.sector_finrank"),
                H("Finite basis and exact dimension"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, Sp,
                    Call("finrank", F.Id("Complex"), Call("sector", F.Id("D"))), Sp, Eq, Sp,
                    Num(4), Sp, Plus, Sp, Num(2), Times, Sp, Call("rank", F.Id("D"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Four ground tensors have ghost subsets empty, {3}, {1,5}, and {1,3,5}. For each matter axis there are two additional tensors: its frequency-one excitation with ghost subset {1}, or with ghost subset {1,3}. The label equivalence is injective and surjective onto the entire proved energy fiber, and its inverse transports the full coefficient equivalence to an explicit basis.")),
                Paragraph(Text("The original integer ghost-number operator has respective eigenvalues 0, 1, 2, and 3 on the four ground tensors, and 1 and 2 on the two tensors for each matter axis. This is a chain-space calculation; its dimension is not a cohomology dimension."))))
        )));
}
