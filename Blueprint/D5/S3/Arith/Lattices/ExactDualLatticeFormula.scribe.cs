using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class ExactDualLatticeFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dual lattice of Lambda^2 A4 is exactly its one-fifth Hodge image.",
        H("Exact Dual-Lattice Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-dual-lattice-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/ExactDualLatticeFormula."
                        + "dual_lattice_eq_one_fifth_hodge_lattice"),
                H("The dual lattice is the one-fifth Hodge image"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("dualLattice"), Sp, Eq, Sp, F.Id("oneFifthHodgeLattice")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lattice L is the integer span of the chosen ordered basis of "
                            + "the real scalar extension of Lambda^2 A4. Its Gram pairing is "
                            + "defined by the displayed six-by-six matrix G. The left-hand "
                            + "side dualLattice consists exactly of the real vectors whose "
                            + "Gram pairing with every vector of L lies in the embedded "
                            + "integer submodule.")),
                    Paragraph(Text(
                        "The right-hand side oneFifthHodgeLattice is the image of every "
                            + "vector of L under the endomorphism represented by J divided "
                            + "by five. Thus the statement is an equality of integral "
                            + "submodules, not merely an equality of determinants, ranks, or "
                            + "cardinalities.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the exact structural theorem that the dual "
                            + "of the integer span of a basis is the integer span of its "
                            + "bilinear dual basis. The local calculation proves that G is "
                            + "nondegenerate and that the six J-over-five basis images are a "
                            + "signed permutation of that dual basis. Signed permutation "
                            + "preserves the complete integer span, yielding the displayed "
                            + "submodule equality without hypotheses."))),
                DescribeRole.Theorem))));
}
