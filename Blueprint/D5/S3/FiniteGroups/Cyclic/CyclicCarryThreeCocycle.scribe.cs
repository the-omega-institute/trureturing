using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Cyclic;

internal sealed class CyclicCarryThreeCocycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cyclic sum recovers the parameter of an explicit carry three-cocycle and vanishes on every two-cochain coboundary.",
        H("Cyclic Carry Three-Cocycle"),
        Blocks(
            Paragraph(Text("For positive n, write a.val for the least nonnegative representative of a in ZMod n. "
                + "Set carry(b,c) = floor((b.val + c.val)/n) and w(t,a,b,c) = t * a * carry(b,c) in ZMod n. "
                + "Raising exp(2πi/n) to the least nonnegative representative of w gives equation (2.13) of David E. Evans and Terry Gannon, "
                + "Reconstruction and Local Extensions for Twisted Group Doubles, and Permutation Orbifolds, arXiv:1804.11145v1.")),
            Describe.Lean(DescribeId.Create("carry-normalization"),
                DeclarationHandle.Create(Prefix + "w_normalized"),
                H("Normalization at the identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representative vanishes whenever any of its three arguments is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("carry-three-cocycle"),
                DeclarationHandle.Create(Prefix + "w_cocycle"),
                H("The three-cocycle identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the trivial action, the inhomogeneous differential of w vanishes. "
                    + "After expansion, it reduces to the equality of the two total carries obtained by parenthesizing a sum of three residues."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("carry-parameter-sum"),
                DeclarationHandle.Create(Prefix + "sum_w"),
                H("Summation recovers the parameter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n greater than one, summing w(t,1,b,1) over b gives t. "
                    + "Only the residue n minus one has carry(b,1) equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("carry-coboundary-detection"),
                DeclarationHandle.Create(Prefix + "difference_is_coboundary_iff"),
                H("Cohomologous carry representatives have equal parameters"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n greater than one, the difference of the representatives with parameters t and u "
                    + "is the coboundary of a ZMod n-valued two-cochain exactly when t = u. Translation by one "
                    + "cancels the two pairs of terms in the coboundary sum for every two-cochain with trivial action, even with arbitrary abelian coefficients. "
                    + "Equal parameters give the zero coboundary."))),
                DescribeRole.Theorem))));
}
