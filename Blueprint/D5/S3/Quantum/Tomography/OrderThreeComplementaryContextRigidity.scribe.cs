using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class OrderThreeComplementaryContextRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A trace-zero order-three unitary cannot split nontrivially across two mutually unbiased diagonal contexts.",
        H("Order-Three Complementary-Context Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("order-three-complementary-contexts-no-split"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity."
                    + "orderThree_complementary_contexts_no_split"),
                H("An order-three unitary has only one nonzero context component"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C and D be complete rank-one contexts in positive complex dimension d. "
                        + "Assume the within-context projectors are pairwise orthogonal and the "
                        + "existing overlap(C,D,i,j) equals 1/d. Let coefficient families a and b "
                        + "each have sum zero, and set A=sum_i a_i P_i, B=sum_j b_j Q_j. "
                        + "If S=A+B satisfies SS*=I and S^3=I, then every a_i is zero or every b_j is zero.")),
                    Paragraph(Text(
                        "The proof reuses RankOneContext and its projection laws. Projecting SS*=I "
                        + "into C gives |a_i|^2=alpha=1-beta, where beta is the average of |b_j|^2. "
                        + "The order-three relation gives S^2=S*. Projecting this relation gives "
                        + "a_i^2+mu=conj(a_i), with mu the average of b_j^2. Summing squared moduli "
                        + "and using sum_i a_i=0 yields alpha^2=alpha+|mu|^2. Therefore "
                        + "alpha beta+|mu|^2=0; nonnegativity forces one coefficient family to vanish.")),
                    Paragraph(Text(
                        "This is a conditional rigidity theorem for an actual matrix decomposition. "
                        + "It does not assume or prove a strict-X completion-affinity lower bound, "
                        + "does not classify common-unbiased roots, and does not exclude four MUBs globally. "
                        + "No rowwise collision threshold is used. A separate geometric adapter must "
                        + "supply the decomposition when consuming a saturated symmetry-plane budget."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula dimension = F.Id("d");
        Formula left = F.Id("C");
        Formula right = F.Id("D");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        return Disp(Seq(
            Apply("MutuallyUnbiasedOrthogonalRankOneContexts", left, right, dimension),
            Sp, Land, Sp, Apply("PositiveDimension", dimension),
            Sp, Land, Sp, Apply("ZeroSumCoefficients", a, b), RowBreak,
            Sp, Land, Sp, Apply("UnitaryOrderThreeSpectralSum", left, right, a, b),
            Sp, Rightarrow, RowBreak,
            Apply("AtLeastOneCoefficientFamilyVanishes", a, b), Dot));
    }
}
