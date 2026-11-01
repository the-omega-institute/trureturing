using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelNearNodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative actual-kernel near-node Schur insertion", H("Quantitative actual-kernel near-node Schur insertion"),
        Blocks(
            Describe.Lean(DescribeId.Create("actualkernelnearnode-h"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.H"),
                H("The actual finite Gram matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every cardinality n and real node map x:Fin(n)->Real, H(i,k)=K(x(i)-x(k))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-b"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.b"),
                H("The actual insertion column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an anchor j and displacement h, b(h)(i)=K(x(i)-x(j)-h)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-s"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.S"),
                H("The actual Schur remainder"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S(h)=M-b(h)^T*H^(-1)*b(h), with M=firstLiMass=K(0). All statements requiring an inverse identity assume the actual H is positive definite."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-u"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.u"),
                H("The anchor-column increment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("u(h)=b(h)-H*e_j, using the actual anchor column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-q"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.q"),
                H("Inverse conditioning mass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("q=1+sum(i,k) abs(H^(-1)(i,k)), so q>=1 without an operator-norm convention."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-scale"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.scale"),
                H("The insertion scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("scale(r)=log(1/r). It is positive at the radii used in the strict certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-rho"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.rho"),
                H("The explicit conditioning-dependent radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rho(x,g,ell)=min(g/2,min(exp(-4*(abs(c)+ell+1)),(8*q(x))^(-2))). Here ell=L(g/2,d,N), g is below the non-anchor gaps, d contains the old and perturbed absolute gaps, and exp(d)<N."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-near-node-remainder"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.near_node_remainder"),
                H("The explicit Schur error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary real actual positive definite configuration, fix g>0 with g<=abs(x(i)-x(j)) at each non-anchor i, d containing abs(x(i)-x(j))+g/2 for every i, and N>exp(d). For 0<r=abs(h)<=min(1/2,g/2), write s=log(1/r), ell=L(g/2,d,N). Then abs(S(h)-(r*s-2*c*r))<=r^2*(4+q*(s/2+abs(c)+ell+2*r)^2). The exact anchor-column identity is S(h)=2*(M-K(r))-u(h)^T*H^(-1)*u(h). The parent cusp estimate abs(R(r))<=2*r^2 supplies the first 4*r^2. The actual compact Lipschitz estimate bounds every non-anchor component by ell*r, including prime-power corners; the anchor component is bounded by the same common envelope using the cusp expansion. An entrywise absolute sum bounds the inverse quadratic form. No arbitrary replacement kernel is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-near-node-positive"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.near_node_positive"),
                H("A positive Schur certificate at the displayed radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same actual configuration and arithmetic window hypotheses, every 0<abs(h)<=rho(x,g,L(g/2,d,N)) satisfies S(h)>=abs(h)*log(1/abs(h))/4>0. The scalar proof establishes s>=4*(abs(c)+ell+1), r<=1/64, q*sqrt(r)<=1/8 and s*sqrt(r)<=1. The last bound follows from exp(s/2)>=s, obtained by squaring exp(s/4)>=1+s/4. Thus the relative error is at most 1/64+9/128=11/128. The stated lower bound follows after paying the linear cusp coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-augmented"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.augmented"),
                H("The augmented actual Gram matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rows and columns are indexed by Fin(n)+Unit. The old points remain x(i), the new point is x(j)+h, and every entry is K evaluated on the corresponding actual point difference."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelnearnode-explicit-near-node-posdef"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelNearNode.explicit_near_node_posDef"),
                H("Insertion for every injective actual configuration"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite injective real node map x, every anchor j and every positive definite actual H, there exist g>0,d,N with the displayed arithmetic bounds, positive explicit rho, and for all 0<abs(h)<=rho both the positive Schur certificate and strict positive definiteness of the augmented actual Gram matrix. The construction takes half the minimum of the positive anchor gaps, using the value one for the anchor itself, and d=g+sum(i) abs(x(i)-x(j)); N=ceil(exp(d))+1 is sufficient. The block argument uses the positive scalar Schur complement to obtain both semidefiniteness and invertibility, then strict definiteness. Mathlib PosDef.fromBlocks_11 alone supplies only semidefiniteness. These radii depend on conditioning, node gaps and the actual finite Mangoldt masses. They provide no uniform prescribed integer insertion, no far-block estimate, and no global RH or Robin conclusion. The displayed quantitative inequalities do not assert the separate asymptotic-equivalence statement."))), DescribeRole.Theorem))));
}
