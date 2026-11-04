using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class TerminalSourceRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both literal fifth histories have full observation rank over every strict source.",
        H("Terminal Source Rank"),
        Blocks(
            Paragraph(Text("Let P=[[r,b],[c,1-r]], with 0<r<1, b,c>0 and bc=r(1-r). Since b>0, c=r(1-r)/b; sourceMatrix(r,b) therefore represents every such source, including nonsymmetric sources and unbounded positive off-diagonal entries. The source has trace one and rank one. These properties concern P and are distinct from the observation ranks below.")),
            Paragraph(Text("The chronological actions are J,M,J,M followed by F in {J,M}. prefixProduct forms each product by left multiplication. tau is the trace of that product times the same source. At the consecutive original clocks 0 through 5 its values are (1,j,T,n,U,V_F), where j=b+c, T=1+b, n=j+r, U=1+2b, V_J=n+r and V_M=n+U. Every value is positive. The initial reading counts and every action is followed by its reading.")),
            Paragraph(Text("The observation matrix has rows (1,tau_i,i tau_i,i² tau_i,i³ tau_i) and acts on the ordinary coefficient vector (d,g₀,g₁,g₂,g₃). The reduced matrix has rows (tau_i−1,i tau_i,i² tau_i,i³ tau_i) at clocks 1 through 5, after y₀=0 implies d=−g₀. The residual drift column is (a₄,a₅,F), where a₄=U Lambda, Lambda=1+6/T+1/U−4/j−4/n and a₅,F=1+V_F(4−15/j+20/T−10/n).")),
            Paragraph(Text("For F=M, StrictDriftVector.drift_vector_nonzero supplies nonvanishing directly. For F=J, clear the positive source denominators and use the common fourth numerator n4 and the fifth J numerator. A polynomial Bezout combination equals 2b⁸(1+b)P_J(b), where P_J is the fourteenth-degree polynomial in the J obstruction. If 0<b<4, group its degrees ten through thirteen as b¹⁰(543416−14256b−6960b²−216b³); this term and all remaining terms are positive. If b≥4, the original fourth-coefficient estimate parentLambda_pos_of_four_le gives Lambda>0. Thus neither fifth history has a common zero of its two residual coefficients.")),
            Paragraph(Text("For a zero perturbation, the first four readings force the gain samples to (−d,−d/j,−d/T,−d/n). ParentCoordinates.polynomial_representation recovers the same whole polynomial from those four values. Its values at clocks four and five, substituted into the final two readings, give a₄d=a₅,F d=0. Residual nonvanishing forces d=0 and then all four samples and the whole polynomial vanish. The observation map is injective. Matrix.rank and LinearMap.finrank_range_of_inj give ranks five, four and one for the full map, its restriction d=−g₀, and the residual column, respectively.")),
            Describe.Lean(
                DescribeId.Create("terminal-source-observation-ranks-and-uniqueness"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/TerminalSourceRank.observation_ranks_and_fixed_source_uniqueness"),
                H("All strict sources and both actual fifth histories"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each F in {J,M}, every 0<r<1 and b>0, the actual six by five observation matrix has rank five, its five by four initial-zero restriction has rank four, and its two by one residual drift column has rank one. For every real C,z,Y,p, the complete compatible history (0,J,24,M,C,J,z,M,Y,F,p) contains at most one original world with that fixed source."))),
                DescribeRole.Theorem),
            Paragraph(Text("OriginalWorld stores the two source coordinates, one real constant drift and four ordinary coefficients of Polynomial.ofFn 4. Compatible requires strict source coordinates, a nonzero whole polynomial and all six literal readings. Subtracting two compatible worlds at the same source gives the zero perturbation just considered; Polynomial.injective_ofFn then identifies the entire coefficient vectors, so the complete worlds agree. No special value of C,z,Y,p enters the proof, and empty fibres are included.")),
            Paragraph(Text("The proof never divides by an unknown gain sample, a leading coefficient, a root difference or a source discriminant. Constant, linear, quadratic and cubic nonzero gains, arbitrary coefficient signs, zero drift, sampled and nonsampled roots, repeated roots, symmetric sources and r=1/2 all remain in scope. Only one selected fifth action is executed in each history. Comparing the two families adds no observation, reset, copy, skipped clock or observer. This is fixed-source uniqueness; it does not recover the source globally, classify arbitrary action words, or assert an effective or stable inverse. The illustrative earlier five-reading singular-source example is a separate assertion.")))));
}
