using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmSymmetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual symmetric three-state qubit ensembles admit explicit optimal POVMs. The two-active optimum remains unique at either equality boundary of the third dual slack.",
        H("Symmetric qubit discrimination and the active-set boundary"),
        Blocks(
            Node("rho", "The actual symmetric ensemble", DescribeRole.Definition,
                "For real a,b,c the three matrices, in plus, minus, third order, are rho_+/-=[[a,+/-b],[+/-b,1-a]] and rho_3=diag(c,1-c). The existing success and pgmScore definitions retain equal original priors 1/3."),
            Node("pairPovm", "The actual two-projector measurement", DescribeRole.Definition,
                "The effects are Q_+=(I+X)/2, Q_-=(I-X)/2, and zero, where X=[[0,1],[1,0]]. These are positive semidefinite rank-one projectors summing to the identity; active means nonzero effect."),
            Node("pairGamma", "The two-active dual certificate", DescribeRole.Definition,
                "Gamma=diag(a+b,1-a+b)/3. Its pair slacks are (b/3)(I-X) and (b/3)(I+X), and its third slack is diag(b-(c-a),b+(c-a))/3. Positivity therefore includes both signs of c-a and the equality boundaries."),
            Node("states_posDef", "Strictly positive actual density matrices", DescribeRole.Theorem,
                "For every real a,b,c with a>0, 0<c<1, and a(1-a)-b^2>0, all three actual matrices are positive definite and have trace one. In particular the scientific strict domain 0<a,c<1 and 0<b<sqrt(a(1-a)) is included; the determinant form does not impose a spectral floor."),
            Node("pair_classification", "Uniqueness throughout the closed two-active region", DescribeRole.Theorem,
                "For every real a,b,c with b>0 and |c-a|<=b, pairPovm is an actual finitePOVM, scores (1+2b)/3, and every actual finitePOVM E is optimal among all actual finitePOVMs if and only if E=pairPovm. The optimization statement is stronger than the density-domain restriction: it needs only b>0 and the displayed absolute-value bound, while states_posDef supplies the physical strict-density domain. The certificate inequality applies to every complex Hermitian-positive effect family, not only real or diagonal competitors. Complementary slackness uses the existing zero_trace_mul_eq_zero supplier. The first two effects lie on the two orthogonal X rays. Completeness equates the third effect's diagonal entries; the sum of its two slack equations forces both to zero because b>0. Positivity then forces that whole effect to zero, including its off-diagonals. Completeness fixes both remaining weights to one. Thus delta=+b and delta=-b retain the same unique pair optimum; a singular third dual slack does not produce an extra optimal effect."),
            Node("upperPovm", "The actual upper three-active effects", DescribeRole.Definition,
                "For t=b/(c-a), the effects are E_+=outer(t,1)/2, E_-=outer(-t,1)/2 and E_3=diag(1-t^2,0). Here outer(v)=v v†. In the strict upper region 0<b<c-a, one has 0<t<1. The effects are positive, sum to I and are all nonzero. This is the positive-sign form of the verification note's Bloch formula; the opposite sign is handled by actual basis permutation in the classification owner."),
            Node("upperGamma", "The upper three-active dual certificate", DescribeRole.Definition,
                "Gamma=diag(c,1-a+b t)/3. Under (c-a)t=b its first slacks are ((c-a)/3) outer(1,-t) and ((c-a)/3) outer(1,t), and its third slack is diag(0,(c-a+b t)/3). These are actual positive matrices and their complementary products with the displayed effects vanish."),
            Node("upper_classification", "Unique optimum in the strict upper three-active region", DescribeRole.Theorem,
                "For every real a,b,c with 0<b<c-a, set t=b/(c-a). The displayed upperPovm is a finitePOVM with score (1+c-a+b t)/3, and an arbitrary actual complex finitePOVM E is optimal if and only if it equals upperPovm. On the strict density domain certified by states_posDef, this is P_opt=(1+R)/3 with R=((c-a)^2+b^2)/(c-a). Complementary slackness puts the first effects on the two tilted rays and the third on the first basis ray; completeness fixes both first weights to 1/2 and the remaining weight to 1-t^2. The endpoint |c-a|=b belongs to pair_classification, which proves uniqueness there separately."),
            Paragraph(Text("Sources and attribution: the anonymous 3 November 2026 mechanism manuscript supplies the earlier two-active setting and its nonstrict pair determinant domain. The 4 November 2026 verification note by Haobo Ma and Wenlin Zhang, in that order, supplies the complete strict-positive classification and both active-set equality boundaries. Hyunho Cha is credited for the symmetric score calculations and the qubit and commuting constructions. CC BY 4.0 applies only to the new Ma-Zhang note; no such grant was supplied for the anonymous mechanism manuscript or the old note, whose literal byline remains Wenlin Zhang and Haobo / trureturing. No source-paper repair, priority, all-pure comparison, or spectral-floor theorem is claimed here."))
        ), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("pgm-symmetric-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")), Blocks(Paragraph(Text(prose))), role);
}
