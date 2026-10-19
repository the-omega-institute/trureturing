using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class EntropyJensenGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite entropy Jensen gaps are nonnegative, homogeneous and jointly convex.",
        H("Finite entropy Jensen gap"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-average"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/EntropyJensenGap.finiteAverage"),
                H("Uniform finite average"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite real family a indexed by S, finiteAverage(a)=sum_s a_s/card(S). The entropy inequalities use nonempty S."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("entropy-jensen-gap"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap"),
                H("Entropy Jensen gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entropy Jensen gap is J(a)=η(av(a))−av(η(a)), where η(u)=−u log u uses the continuous value η(0)=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("entropy-jensen-gap-laws"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap_laws"),
                H("The full nonnegative cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a nonempty finite index type S, let av(a)=sum_s a_s/card(S) and η(u)=−u log u, with η(0)=0. The gap J(a)=η(av(a))−av(η(a)) is nonnegative, satisfies J(ca)=cJ(a) for c≥0, and is jointly convex for all nonnegative real vectors.")),
                    Paragraph(Text("Nonnegativity is finite Jensen applied to the concave function η. The product identity η(cx)=xη(c)+cη(x) gives homogeneity. For nonzero means A=av(a) and B=av(b), normalize by A and B. Concavity of η with weights A/(A+B), B/(A+B), followed by averaging and multiplication by A+B, gives J(a+b)≤J(a)+J(b). Zero mean forces every nonnegative coordinate to vanish. Subadditivity and homogeneity yield joint convexity, including all boundary faces."))), DescribeRole.Theorem))));
}
