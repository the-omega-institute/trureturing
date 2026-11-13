using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.PhysicalLie;

internal sealed class LatticeMatterGhostHermitianDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticematterghosthermitian-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Hermitian form on the original matter-ghost tensor states", H("Ordinary Hermitian form on the original matter-ghost tensor states"), Blocks(
            Paragraph(Text("Let D : LatticeData. State D is the original algebraic tensor Carrier D tensor the original countable bc occupation Fock space. Hm and Hg are the existing ordinary Hermitian forms. All states, charges, ranks and integer modes retain their original ranges; finite supports belong to the individual algebraic states.")),
            Paragraph(Text("Source placement revision: the two original subtraction helper names Hmg_sub_left and Hmg_sub_right are absent from this first module and its Reg and declaration-description inventories. Their exact public statements and proofs are retained once in the saved future PhysicalPairing source, under their original qualified namespace, next to their original inserted_sub_left/right consumers. That later source is deferred and has not been applied or accepted.")),
            Node("Hmg", "The original tensor Hermitian form", "For every D and x,y : State D, Hmg x y is the double finite-support sum Hm v w * Hg (ket S) (ket T) over the actual ghost-basis slices of x and y.", DescribeRole.Definition),
            Node("Hmg_zero_left", "Zero in the first argument", "For every D and y : State D, Hmg 0 y = 0.", DescribeRole.Theorem),
            Node("Hmg_zero_right", "Zero in the second argument", "For every D and x : State D, Hmg x 0 = 0.", DescribeRole.Theorem),
            Node("Hmg_add_left", "Additivity in the first argument", "For every D and x,z,y : State D, Hmg (x+z) y = Hmg x y + Hmg z y.", DescribeRole.Theorem),
            Node("Hmg_smul_left", "Conjugate linearity in the first argument", "For every D, a : Complex and x,y : State D, Hmg (a smul x) y = star a * Hmg x y.", DescribeRole.Theorem),
            Node("Hmg_hermitian", "Ordinary Hermitian symmetry", "For every D and x,y : State D, Hmg x y = star (Hmg y x).", DescribeRole.Theorem),
            Node("Hmg_add_right", "Additivity in the second argument", "For every D and x,y,z : State D, Hmg x (y+z) = Hmg x y + Hmg x z.", DescribeRole.Theorem),
            Node("Hmg_smul_right", "Linearity in the second argument", "For every D, a : Complex and x,y : State D, Hmg x (a smul y) = a * Hmg x y.", DescribeRole.Theorem),
            Node("Hmg_tmul", "The original pure-tensor formula", "For every D, v,w : Carrier D and u,z : the original Fock, Hmg (v tensor u) (w tensor z) = Hm v w * Hg u z.", DescribeRole.Theorem),
            Node("Hmg_ghostB", "Adjoint of every b mode", "For every D, m : Int and x,y : State D, Hmg (ghostB D m x) y = Hmg x (ghostB D (-m) y).", DescribeRole.Theorem),
            Node("Hmg_ghostC", "Adjoint of every c mode", "For every D, m : Int and x,y : State D, Hmg (ghostC D m x) y = Hmg x (ghostC D (-m) y).", DescribeRole.Theorem),
            Node("Hmg_ghostCharge", "Adjoint of the actual lifted cubic charge", "For every D and x,y : State D, Hmg (ghostCharge D x) y = Hmg x (ghostCharge D y), with ghostCharge the tensor lift of the actual cubic Qg.", DescribeRole.Theorem),
            Node("Hmg_matterMode", "Adjoint of every matter mode", "For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every m : Int and x,y : State D satisfy Hmg (matterMode D H m x) y = Hmg x (matterMode D H (-m) y).", DescribeRole.Theorem),
            Node("Hmg_T", "Adjoint of the locally finite coupling", "For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every x,y : State D satisfy Hmg (T D H x) y = Hmg x (T D H y). The proof uses a common statewise finite capture closed under m maps to -m.", DescribeRole.Theorem),
            Node("Hmg_totalCharge", "Adjoint of the original total charge", "For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every x,y : State D satisfy Hmg (totalCharge D H x) y = Hmg x (totalCharge D H y), with totalCharge D H = T D H + ghostCharge D.", DescribeRole.Theorem),
            Paragraph(Text("The source retains the suppliers and attribution Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Mathlib, Batteries, and the original BRST literature. This tensor extension reuses their existing factor-adjoint theorems. These descriptions identify the repository construction and do not assert literature priority.")))));
}
