using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CountableHankelIntegerFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer bases for complete-spectrum negative subspaces",
        H("Integer bases for complete-spectrum negative subspaces"),
        Blocks(Describe.Lean(
                DescribeId.Create("exists-integer-negative-family"),
                DeclarationHandle.Create("D5/S3/Constants/Moments/CountableHankelIntegerFamily.exists_integer_negative_family"),
                H("Every nonzero real combination of one integer family is negative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every index type iota, complex node and weight maps z,w, and permutation c, assume every node has norm at most one, z is injective, z(c(i)) is conjugate(z(i)), w(c(i)) is conjugate(w(i)), the norms of all weights are summable, and every positive-radius node superlevel set is finite. For every natural k and selector s from Fin k to iota, require s injective, s(a) unequal to c(s(b)) for every a,b, and every selected weight nonzero. There exist a natural N and one integer matrix U on Fin k by Fin(N+1) such that, for every nonzero real vector t, the complete sum over all i of w(i) times the ordinary complex square of sum_j t(j) sum_a U(j,a) z(i) to power a has strictly negative real part. The map taking t to its real coefficient vector a mapped to sum_j t(j) U(j,a) is injective. The same U works for every t. The empty family k=0 is included.")),
                    Paragraph(Text("The uniform real negative family is reconstructed at one degree bound equal to the maximum of all row degrees. The original quadratic_identity expands the complete absolutely summable form at the combined coefficient vector, giving the full moment Hankel matrix. Simultaneous matrix approximation preserves negativity for all coefficient directions, and a common matrix denominator gives integer coefficients. If two real vectors had identical coefficients, their difference would have zero form, contradicting strict negativity unless they were equal.")),
                    Paragraph(Text("All original nodes, conjugate weights and the entire infinite tail remain. Individually negative rows would not suffice. This conditional k-dimensional construction neither establishes existence of selected off-axis pairs nor proves RH; analytic multiplicities at an identical folded node remain represented only by their aggregated weights. No effective uniform degree bound is claimed."))),
                DescribeRole.Theorem))));
}
