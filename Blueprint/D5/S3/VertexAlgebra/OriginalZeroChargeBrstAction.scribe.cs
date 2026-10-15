using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeBrstActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordered ghost stress and BRST sums on the complete nonpositive ghost energy fiber.",
        H("Signed Original Ghost Calculation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-low-ghost-double-sum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.ghostDoubleSum_nonpositive"),
                H("Exact signed ghost action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("S"), Comma, Sp,
                    Call("energy", F.Id("S")), Sp, Le, Sp, Num(0), Sp, Rightarrow, Sp,
                    Call("ghostDoubleSum", Call("single", F.Id("S"), Num(1))), Sp, Eq, Sp,
                    Call("lowEnergyGhostAction", F.Id("S"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The action is four times the {1,5} basis vector for S={3}, twice the {1,3} vector for S={1}, and zero for every other nonpositive-energy subset. The support theorem proves that these cases exhaust the native exterior Fock states at these energies.")),
                Paragraph(Text("This is the sum before multiplication by one half in the original Q. The proof uses the actual ghost L modes, the original normalPair ordering threshold, and the exterior insertion and erasure signs. Support bounds reduce each already finite original sum to an explicit rectangle; no occupation cutoff is assumed.")))),
            Describe.Lean(
                DescribeId.Create("original-q-tensor-split"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction.Q_tmul_split"),
                H("Original tensor charge"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Q", F.Id("D"), F.Id("H"), Call("tensor", F.Id("u"), F.Id("g"))), Sp, Eq, Sp,
                    Call("matterGhostSum", F.Id("u"), F.Id("g")), Sp, Plus, Sp,
                    Open, Num(1), Slash, Num(2), Close, Times, Sp,
                    Call("tensor", F.Id("u"), Call("ghostDoubleSum", F.Id("g")))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The matter term is the sum over every integer n of L(n)u tensor c(-n)g. The second term is the original ordered ghost sum, not an auxiliary delta. The existing statewise finite support laws justify splitting and transporting the sums on arbitrary actual tensor states."))))
        )));
}
