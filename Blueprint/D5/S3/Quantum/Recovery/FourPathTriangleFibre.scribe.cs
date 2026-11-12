using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathTriangleFibreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coupled support inequality for the original radical on the complete attained triangle.",
        H("Four-path closed triangle fibre"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-triangle"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.Triangle"),
                H("The complete attained triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain consists of all X and Y in [0,1] with sqrt(X)+sqrt(Y) at least L. Both box and trace constraints are inclusive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-z"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.Z"),
                H("The original normalized trace coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Z(L,X,Y)=(L²−X−Y)/(2 sqrt(XY)). The triangle hypotheses with L>1 imply X>0 and Y>0, so this denominator is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-f"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.F"),
                H("The original nonnegative fibre radical"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("F(L,X,Y)=sqrt((1−X)(1−Y)(1−Z(L,X,Y)²)). Its radicand is nonnegative on the complete triangle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-b"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.B"),
                H("The box cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B(u)=(2−u)²."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-d"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.D"),
                H("The trace cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D(a,u)=a(2u−a)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-w"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.W"),
                H("The central fibre width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W(a,u)=B(u)D(a,u)/u²."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-t"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.T"),
                H("The coupled support cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("T(a,u)=W(a,u) when u≤1, and min(B(u),D(a,u)) when u>1. The low-half value relaxes the sharper tangent cap by using kappa≥1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-triangle-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.triangle_geometry"),
                H("The exact original radical identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, X>0, Y>0 and u=X+Y>0. Put t=Y−X and a=L². Then t²<u², t²≤B(u), t²≤D(a,u), Z(L,X,Y)²≤1, and 4F(L,X,Y)²(u²−t²)=(B(u)−t²)(D(a,u)−t²)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-closed-triangle-ball"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_ball"),
                H("A circular relaxation on the complete triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, (Y−X)²+(2F(L,X,Y))²≤T(L²,X+Y). The bound includes zero-width fibres without a limiting argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-triangle-fibre-closed-triangle-fibre"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathTriangleFibre.closed_triangle_fibre"),
                H("Closed triangle fibre inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real L,X,Y with L>1, L²≤2 and (X,Y) in the complete attained triangle, set a=L² and u=X+Y. Then T(a,u) and W(a,u) are nonnegative and W(a,u)(Y−X)²+T(a,u)(2F(L,X,Y))²≤T(a,u)W(a,u). No positivity assumption on T or W is imposed. The bound therefore includes vanishing-width fibres and all triangle boundaries. The proof uses the exact identity 4F²(u²−(Y−X)²)=(B−(Y−X)²)(D−(Y−X)²). For u≤1 this yields (Y−X)²+4F²≤W; for u>1 the two possible orders of B and D give the chord bound."))),
                DescribeRole.Theorem))));
}
