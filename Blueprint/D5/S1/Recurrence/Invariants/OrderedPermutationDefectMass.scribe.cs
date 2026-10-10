using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class OrderedPermutationDefectMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine floor lower bound and a reflected permutation force opposite-rank capacity and quadratic total defect.",
        H("Ordered Permutation Defect Mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-permutation-defect-mass-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Invariants/OrderedPermutationDefectMass.result"),
                H("Opposite ranks and the complete defect chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let t and c be real with 0 < t < 1, let r be an integer, and let A be "
                        + "a finite set of p >= 1 distinct integers. Let f be integer-valued on A, "
                        + "put g(z)=floor(t*z+c), and assume g(z) <= f(z) for every z in A. "
                        + "Assume the actual map z to r-f(z) is a bijection from A to A.")),
                    Paragraph(Text(
                        "Write the increasing enumeration as z_1 < ... < z_p, put gamma=1-t, "
                        + "m=floor(p/2), and S=sum over z in A of f(z)-g(z). Then every "
                        + "1 <= i <= p satisfies z_(p+1-i)+g(z_i) <= r. Moreover, "
                        + "S >= sum from i=1 to m of floor(gamma*(z_(p+1-i)-z_i)) "
                        + ">= sum from i=1 to m of floor(gamma*(p+1-2*i)) "
                        + ">= gamma*floor(p^2/4)-m >= gamma*p^2/4-p/2. "
                        + "Empty sums are zero. Integer sums are cast to the reals for the final comparisons.")),
                    Paragraph(Text(
                        "The formal enumeration uses zero-based Fin p. Source rank i+1 has "
                        + "opposite rank p-i, represented by Fin.rev. The first m indices are "
                        + "embedded from Fin m into Fin p. No monotonicity of f or reversal "
                        + "of the actual permutation is assumed.")),
                    Paragraph(Text(
                        "Each suffix has distinct images below its first envelope threshold; "
                        + "its cardinality forces the opposite-rank inequality. The virtual "
                        + "slack r-g(z_i)-z_(p+1-i) is nonnegative. Its full sum equals S by "
                        + "permutation invariance of the sum, although individual virtual "
                        + "slacks need not equal actual point defects. Disjoint opposite-rank "
                        + "pairs give the first floor sum, retaining a nonnegative central "
                        + "slack when p is odd. Integer spacing gives the second sum, and "
                        + "its rank distances sum to floor(p^2/4)."))),
                DescribeRole.Theorem)),
        []));
}
