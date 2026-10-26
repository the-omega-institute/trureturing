using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class SourceCompactificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original source remains 0<r<1 and b>0, with no upper bound on either positive offdiagonal",
        H("SourceCompactification"),
        Blocks(
        Paragraph(Text("The original source remains 0<r<1 and b>0, with no upper bound on either positive offdiagonal. The auxiliary variables x=b/(1+b), k=j/(1+j), u=j/(j+n) and t=b/j record rates lost by simply adjoining b=0 or b=∞. They are derived coordinates, not a normalization of the source or a restriction of the world.")),
        Paragraph(Text("The compact source is the unit box in (r,x,k,u,t) cut out by five polynomial identities: r(1-r)(1-x)²(1-k)=x(k-x); x(1-k)=tk(1-x); r(1-k)u=k(1-2u); (1-2u)(1-r)(1-x)=ux(1-t); r(1-r)(1-x)²t=x²(1-t). Every actual strict source satisfies all five identities.")),
        Paragraph(Text("Write v=(1+r)(1-k)+2tk+k and ℓ=(8-6x²)k(1-u)-4(1-k)(1+x). The other coefficient is α=(1-k)k(1-u)+v((24-20x)k(1-u)-(15-5u)(1-k)). The pair (ℓ,α) is nonzero everywhere on this entire compact set. For 0<x,k<1 it is a nonzero rescaling of (Λ,A₅) at b=x/(1-x). Cases k=0, k=1 and x=0 are proved from the polynomial relations, including both r endpoints.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-closedsource-iscompact"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceCompactification.closedSource_isCompact"),
            H("closedSource isCompact"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The set of all five-coordinate points satisfying ClosedSource is compact: it is the closed subset of the unit box defined by the five polynomial source identities."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-compactsource-mem"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceCompactification.compactSource_mem"),
            H("compactSource mem"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every strict source 0<r<1 and b>0, compactSource(r,b) satisfies ClosedSource. The positive offdiagonals have no imposed upper bound."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-compact-drift-vector-nonzero"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SourceCompactification.compact_drift_vector_nonzero"),
            H("compact drift vector nonzero"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At every point of ClosedSource, ℓ≠0 or α≠0. This includes all boundary points of the compact source and ensures ℓ²+α²>0 throughout it."))),
            DescribeRole.Theorem))));
}
