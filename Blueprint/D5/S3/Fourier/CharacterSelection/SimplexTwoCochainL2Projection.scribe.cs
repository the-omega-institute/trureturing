using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class SimplexTwoCochainL2ProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact squared-energy projection and optimal coefficient for alternating ordered triangle cochains.",
        H("Ordered Simplex Two-Cochain Energy and Optimal Coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contraction"),
                DeclarationHandle.Create(Prefix + "contraction"),
                H("Triangle contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite vertex type V and a real triangle cochain F, "
                    + "S(i,j) is the sum of F(r,i,j) over every r in V."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("average-edge"),
                DeclarationHandle.Create(Prefix + "averageEdge"),
                H("Averaged edge cochain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n=|V|, the edge cochain a(i,j) is S(i,j)/n. "
                    + "The energy theorem assumes V is nonempty, so this denominator "
                    + "is nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-coboundary"),
                DeclarationHandle.Create(Prefix + "edgeCoboundary"),
                H("Edge coboundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The triangle coboundary of an edge cochain a is "
                    + "da(i,j,k)=a(j,k)-a(i,k)+a(i,j)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tetra-defect"),
                DeclarationHandle.Create(Prefix + "tetraDefect"),
                H("Tetrahedral defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a triangle cochain F, dF(r,i,j,k)="
                    + "F(i,j,k)-F(r,j,k)+F(r,i,k)-F(r,i,j)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tetra-defect-energy-and-optimality"),
                DeclarationHandle.Create(Prefix + "tetra_defect_energy_eq_and_optimal"),
                H("Exact tetrahedral energy and optimal coefficient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("F"), Sp, InMacro, Sp, Mathcal, Grp(F.Id("A")),
                    Comma, Sp, F.Id("T"), Open, F.Id("F"), Close, Sp, Eq, Sp,
                    D(4), F.Id("n"), F.Id("E"), Open, F.Id("F"), Close, Close,
                    Quad, Land, Quad, Open, F.Id("n"), Sp, Geq, Sp, D(4), Sp,
                    Implies, Sp, Forall, Sp, F.Id("C"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Open, Forall, Sp, F.Id("F"), Sp, InMacro, Sp, Mathcal, Grp(F.Id("A")),
                    Comma, Sp, F.Id("T"), Open, F.Id("F"), Close, Sp, Leq, Sp,
                    F.Id("C"), F.Id("E"), Open, F.Id("F"), Close, Close, Sp,
                    Implies, Sp, D(4), F.Id("n"), Sp, Leq, Sp, F.Id("C"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be any nonempty finite vertex type, n=|V|, and F a real "
                        + "triangle cochain. Assume F(j,i,k)=-F(i,j,k) and "
                        + "F(i,k,j)=-F(i,j,k) for every i,j,k. Let A be the set of "
                        + "all such alternating cochains. With S, a, da, and dF as "
                        + "above, define T(F) as the sum of dF(r,i,j,k)^2 over all "
                        + "ordered quadruples and E(F) as the sum of "
                        + "(F(i,j,k)-da(i,j,k))^2 over all ordered triples. Both sums "
                        + "include repeated vertices, and a is the averaged edge "
                        + "cochain of the particular F. No cocycle or exactness "
                        + "hypothesis is imposed.")),
                    Paragraph(Text(
                        "For every alternating F, T(F)=4n E(F). If n>=4 and a real "
                        + "constant C satisfies T(F)<=C E(F) for every alternating F, "
                        + "then 4n<=C. When n>=4, 4n is the least admissible real "
                        + "coefficient, and for each C<4n an alternating cochain "
                        + "violates the bound.")),
                    Paragraph(Text(
                        "The residual R=F-da is alternating and its sum over any one "
                        + "vertex vanishes. The edge coboundary has zero tetrahedral "
                        + "defect, so dF=dR. Expanding the four face terms gives four "
                        + "diagonal sums, each n times the squared norm of R. Each of "
                        + "the six mixed sums vanishes by a zero contraction. Thus the "
                        + "defect energy is exactly 4n times the residual energy.")),
                    Paragraph(Text(
                        "For optimality when n>=4, choose four distinct vertices "
                        + "p0,p1,p2,p3 in V. Define u(x), v(x), and w(x) to be 1 at p1,p2,p3, "
                        + "respectively, and 0 elsewhere. The determinant cochain is "
                        + "F(i,j,k)=u(i)v(j)w(k)+u(j)v(k)w(i)+u(k)v(i)w(j)"
                        + "-u(i)v(k)w(j)-u(j)v(i)w(k)-u(k)v(j)w(i). Swapping either "
                        + "adjacent pair changes its sign. It has F(p1,p2,p3)=1 and "
                        + "vanishes whenever an argument is p0. Hence "
                        + "dF(p0,p1,p2,p3)=1, so T(F)>0. The energy equality and "
                        + "4n>0 imply E(F)>0. Applying the universal C-bound to this "
                        + "cochain and cancelling its positive residual energy "
                        + "gives 4n<=C.")),
                    Paragraph(Text(
                        "The complete-simplex spectral setting is classical. "
                        + "The theorem states its ordered-sum normalization, "
                        + "averaged edge reconstruction, and optimal coefficient."))),
                DescribeRole.Theorem))));
}
