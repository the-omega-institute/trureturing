using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DerivativeLayerGramianPositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive polynomial derivative-layer Gramian", H("Positive polynomial derivative-layer Gramian"), Blocks(
            Describe.Lean(DescribeId.Create("derivative-layer-gramian-pos"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos"),
                H("Positive polynomial derivative-layer Gramian"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.")),
                    Paragraph(Text("Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.")),
                    Paragraph(Text("Define A(j)=c composed with b^j composed with Pi(j) composed with i, P(s)=sum over j<n of s^j/j! A(j), and H=the interval integral from zero to one of P(s) adjoint composed with P(s). The integral is the actual operator-valued Bochner interval integral.")),
                    Paragraph(Text("The quadratic form of H is strictly positive at every nonzero x in U. In zero dimension this universal assertion is vacuous.")),
                    Paragraph(Text("Zero integrated squared polynomial norm implies zero polynomial on the interval. Scalar polynomial coefficient uniqueness makes every A(j)x zero. A projected layer vector then belongs both to N(j+1) and its orthogonal complement; resolving the entire filtration forces x=0.")),
                    Paragraph(Text("The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        return Disp(Seq(Forall, Sp, x, InMacro, Sp, F.Id("U"), Comma, Sp,
            x, Neq, Sp, D(0), Sp, Rightarrow, Sp, D(0), Lt,
            Langle, Sp, x, Comma, App(F.Id("H"), x), Rangle));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
