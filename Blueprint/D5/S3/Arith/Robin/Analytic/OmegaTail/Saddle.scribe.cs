using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class SaddleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimized distinct-prime rate has a unique saddle between one and two, and its minimum equals the entropy at that saddle.",
        H("The entropy saddle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.m"),
                H("Logarithmic moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moment m(s) is log(a(s))-(pi/s)*cot(pi/s), where a(s)=s*sin(pi/s)/pi and s>1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("entropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.H"),
                H("Entropy expression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entropy expression is H(s)=s-pi*cot(pi/s)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("least-rate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.C0"),
                H("The least exponential rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C_0 is the infimum of F_0(s)=s*(1-log(a(s))) over all real s>1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("saddle"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.saddle"),
                H("The zero-moment parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The saddle is chosen as a zero of m in the interval (1,2). Existence follows from the intermediate value theorem between 4/3 and 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("characterization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.saddle_characterization"),
                H("Unique zero and global minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The saddle lies strictly between one and two, has zero log moment, and is the unique zero throughout s>1. The optimized rate attains its global minimum there, with C_0=F_0(saddle)=H(saddle). Differentiating m gives (1/s)*(1-(pi/s)^2/sin(pi/s)^2), which is strictly negative because 0<sin(t)<t for t=pi/s in (0,pi). Differentiating F_0 gives -m, so the derivative changes from negative to positive at this unique zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-gap"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.constant_gt_one"),
                H("The minimum exceeds one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The minimum rate C_0 strictly exceeds one: a(s)<1 on s>1, so F_0(saddle)>saddle>1. No decimal enclosure is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.m_neg_of_saddle_lt"),
                H("Strict logarithmic budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every parameter strictly to the right of the saddle has negative log moment, providing strict slack for selecting prime products below the original cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-continuity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle.H_continuousAt"),
                H("Continuity of the entropy expression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H is continuous at every real parameter s>1. In particular H(s) tends to H(saddle) as s decreases to the saddle from above."))),
                DescribeRole.Theorem))));
}
