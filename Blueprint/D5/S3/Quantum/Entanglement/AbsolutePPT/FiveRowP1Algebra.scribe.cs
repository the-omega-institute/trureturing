using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiveRowP1AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial coordinates for the five-row scalar inequalities.",
        H("FiveRowP1Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-hyp"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.Hyp"),
                H("Unchanged manuscript scalar necessary inequalities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-necessary-sound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.necessary_sound"),
                H("Necessary polynomial projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-fixed-sound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.fixed_sound"),
                H("Eight necessary upper envelopes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-target-left"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.target_left"),
                H("Continuous left endpoint reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-target-right"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.target_right"),
                H("Continuous right endpoint reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiverowp1algebra-vertex-value"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Algebra.vertex_value"),
                H("Square completion reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fifteen rational coefficients encode the quadratic expressions in r, H, D and q. The scalar hypotheses include all budget, cap and tail inequalities. Exact evaluation identities connect the endpoint and vertex polynomials to the energy gap for every real j."))), DescribeRole.Theorem))));
}
