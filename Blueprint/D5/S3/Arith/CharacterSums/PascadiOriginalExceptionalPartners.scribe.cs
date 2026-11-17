using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalExceptionalPartnersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The identically zero integer-pencil stratum has a uniform subpower count of actual ordered endpoint pairs, including aligned retained baselines.",
        H("Actual zero-polynomial partners"),
        Blocks(
            Paragraph(Text("Write l_z(T)=z1+z2*T, L=l_base1+l_base2-l_q and Q=l_base1*l_base2. The original integer pencil of e=(x,y) is P_e=L*l_x*l_y-(l_x+l_y-l_q)*Q. This module counts the actual integer endpoint pairs for which P_e=0 as an integer polynomial. That condition is stronger than coefficientwise zero reduction modulo p; nonzero content-p pencils are a separate stratum.")),
            Describe.Lean(DescribeId.Create("pascadi-original-zero-polynomial-partners-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalExceptionalPartners.actual_zero_polynomial_partners_subpower"),
                H("A uniform count of actual integer-zero partners"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every epsilon>0, one positive constant C works before the choice of prime p, original units a1,a2, actual middle congruence basis B, retained baseline, scales and finite partner set S. Assume 1<=J2<=J1; the anchor and baseline obey their coordinate bounds; the baseline satisfies the original WordSolution; retain units R1, the negative second physical anchor coordinate, w, both baseline first physical coordinates and the original shifted anchor expression. Both physical endpoints of every e in S lie in the literal rectangle |u|<=X, |z|<=Y, with 2X<p^3 and 2Y<p^3. If every integer pencil is identically zero, (J1*J2)^5<=M^5*p^3 and (24*(8*18)^4)^5*M^40<p, then card(S)<=C*p^epsilon. No nonalignment premise or physical multiplicity factor is needed.")),
                    Paragraph(Text("Choose the canonical integer lift b of beta=V1/R1 modulo p^3. The actual integer values V_x(b)=(-Q+L*l_x)(b) and V_y(b) multiply to the fixed D=Q(b)*(Q-L*l_q)(b). The original unit observations imply D is nonzero. The original cap and cutoff bound its absolute value by p^24; the signed-divisor bound at exponent epsilon/24 therefore controls all value pairs uniformly. Equal values cancel the genuine nonzero L(b), hence give equal linear observations modulo p^3. The physical rectangle and congruence lattice recover the actual physical endpoints, and uniqueness of coordinates in B recovers x and y. The resulting integer value-pair code is proved injective on the actual set S."))),
                DescribeRole.Theorem),
            Paragraph(Text("The problem and polynomial pencil are attributed to Pascadi. This closes the literal integer-zero partner count on the stated retained chart. Coefficientwise zero reduction, the full derivative-zero layer, parameter averaging, exceptional unit charts and restoration of the original six-variable count require their own arguments. The full original conjecture remains open here; no worldwide-priority or author-acceptance claim is made.")))));
}
