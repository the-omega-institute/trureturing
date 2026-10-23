using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class OriginalAbsenceDoubleZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Originally absent native addresses give two zero existence replies at every positive even epoch.",
        H("Original absence and the two label probes"), Blocks(
            Paragraph(Text("A source is an arbitrary finite nonempty ordered full binary tree with Boolean leaf labels. True denotes alpha and false denotes beta. Native substitution sends alpha to beta and beta to pair(beta,alpha), distributing through every pair. Addresses are finite Boolean lists, with false denoting left and true denoting right. The four-valued readout returns absent whenever navigation fails.")),
            Describe.Lean(
                DescribeId.Create("originalabsencedoublezero-original-absence-double-zero"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/OriginalAbsenceDoubleZero.original_absence_double_zero"),
                H("The full original-absence double-zero law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every source u, every natural k with k at least one, and every complete address p, if readout(p,u)=absent, then readout(p followed by rights(k-1) followed by left,left, substitution iterated 2k times on u)=absent and readout(p followed by rights(k) followed by left, substitution iterated 2k times on u)=absent. There is no hypothesis that p or its parent was originally present, or that p is currently present.")),
                    Paragraph(Text("Write T(j) for substitution iterated j times on alpha. The proof tracks an originally missing address through successive epochs. If it first appears in one substitution, its subtree is alpha or beta, namely T(0) or T(1). An already present subtree transports under substitution; thus, when the originally absent address is currently present, its actual subtree equals some T(j) with j at most the elapsed epoch. If the address is still missing, both extended readouts are absent directly by concatenated navigation.")),
                    Paragraph(Text("The atomic trees satisfy T(j+2)=pair(T(j+1),T(j)). An induction on the number of right steps shows that, for j at most 2(s+1), both rights(s) followed by left,left and rights(s+1) followed by left are absent in T(j). At s=0, the only ranks are zero, one and two, and both paths fail directly. Each successful first right step reduces the atomic rank by two, so the induction applies. Concatenated readout transports these exclusions back to the full original prefix p.")),
                    Paragraph(Text("Both probes read the same stationary tree, substitution iterated 2k times on u. Their absent replies give zero under the existence projection of the original paid readout. The mathematical law adds no free observation port, source advice, finite horizon, source-size bound, register update, decoder or optimal-cost assertion."))
                ), DescribeRole.Theorem)
        )));
}
