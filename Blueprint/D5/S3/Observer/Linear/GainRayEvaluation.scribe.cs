using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct clocks and polynomial coefficient evaluation", H("Distinct clocks and polynomial coefficient evaluation"), Blocks(
            Paragraph(Text("evaluation(d,n,t) has entries t(i) to the power k for i in Fin n and k in Fin(d+1), with the usual convention that a zeroth power is one. evaluate is its real linear multiplication map on ordinary coefficients. It is exactly evaluation of gain d beta at the specified nodes.")),
            Paragraph(Text("The nodes are explicit. clocks n i is the real cast of the original natural index i. Interpolation at arbitrary distinct nodes is an algebraic interface; literal acquisition continues to use every consecutive original clock. The zero-node case and the empty value vector are included.")),
            Paragraph(Text("evaluationRightInverse chooses a right inverse from evaluation_surjective whenever n<=d+1 and t is injective. No nonzero-gain promise is used in this linear interpolation interface. A compatible legal-world construction must separately ensure the whole coefficient vector is nonzero.")),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayevaluation-evaluation-injective"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayEvaluation.evaluation_injective"),
                H("Enough distinct clocks determine all coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d,n and t:Fin n to the reals, injectivity of t and d+1<=n imply injectivity of evaluate d n t. Two coefficient vectors with these evaluations equal represent polynomials of degree less than d+1 agreeing at n distinct nodes, so they coincide."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayevaluation-evaluation-surjective"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayEvaluation.evaluation_surjective"),
                H("Every short vector of prescribed values occurs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d,n and injective t:Fin n to the reals, n<=d+1 implies surjectivity of evaluate d n t. Lagrange interpolation supplies a polynomial of degree less than n; its first d+1 coefficients give the witness. For n=0 the unique empty vector is attained by zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayevaluation-pureJ-history-surjective"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayEvaluation.pureJ_history_surjective"),
                H("Coefficient-and-drift history extension is onto"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d,n with n<=d+1, the map from Coeff d times the reals to real Fin n vectors, sending (beta,delta) to the vector gain(d,beta)(clocks n i)+delta, is surjective. The witness may take drift zero. This is the extension to the full coefficient space; it does not claim nonzero-gain fiber completion."))), DescribeRole.Theorem))));
}
