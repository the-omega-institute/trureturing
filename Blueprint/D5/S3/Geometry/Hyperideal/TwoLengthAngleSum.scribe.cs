using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class TwoLengthAngleSumDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/TwoLengthAngleSum.two_length_angle_sum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The selected edges of a two-length generalized tetrahedron have a strict total-angle lower bound on the full unbounded parameter domain.",
        H("Two lengths and the sum over actual selected edge positions"),
        Blocks(
            Paragraph(Text("A and B are cosine-length coordinates, with A>1 and B>4A+5. The six local positions have the original order (12,13,14,34,24,23). S is any subset of these six positions with at least two elements; position j reads B exactly when j is in S and otherwise reads A. Cardinality counts positions, so repeated global labels do not collapse local occurrences.")),
            Paragraph(Text("For a six-vector x and target position q, use the existing FourCycleCurvature.frame to read the target, four neighbors and opposite coordinate in the original FourCycleEnvelopes.cosine. Thus the raw cosine is the original numerator divided by the two positive square roots. extendedAngle(x,q) is arccos(max(-1,min(rawCos(x,q),1))). AngleSum(A,B,S) abbreviates the sum of these extended angles over every q in S, with x(j)=B for j in S and A otherwise. card(S) denotes its finite cardinality.")),
            Describe.Lean(
                DescribeId.Create("positive-native-radicand"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/TwoLengthAngleSum.rad_positive"),
                H("Positive radicands on the full positive coordinate domain"),
                StatementSource.FromAuthor(F.Disp(RadicandStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For three independent real coordinates greater than one, the original rad(x,y,z)=2xyz+x^2+y^2+z^2-1 is strictly positive. This is the denominator-positivity supplier used by the native six-coordinate classification and local budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-length-continuous-angle-sum"),
                DeclarationHandle.Create(Declaration),
                H("The complete selected-edge sum exceeds one quarter pi per occurrence"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof establishes the missing continuous cosine bounds from the actual numerator and radicands. Write a=A-1 and b=B-4A-5, so both are positive and B=9+4a+b. For each useful edge, the negative-numerator alternative or squared-denominator gap is exactly a polynomial with positive coefficients and a positive constant term. These certificates prove the inequalities for every real parameter in the stated unbounded region; no desired cosine or angle bound is assumed.")),
                    Paragraph(Text("There are 57 selected-edge subsets of size at least two, grouped into nine K4 graph types. Adjacent pairs, triangles and four-cycles use every selected angle above pi/3. Opposite pairs use two angles above pi/2; stars and the all-six type use every selected angle above pi/4. A three-edge path uses its two endpoints above pi/2. The four-edge graph complementary to an adjacent pair uses its selected opposite pair above pi/2. A five-edge graph uses the four edges adjacent to the missing edge above pi/3. The finite slot routing checks every actual subset directly. Adding the other nonnegative extended angles gives the complete sum with all its multiplicities.")),
                    Paragraph(Text("For A=2, B=14 and the path S={0,3,5}, the middle position 5 has raw numerator 2466, both radicands 1179, and raw cosine 274/131>1. Its extended angle is zero, while the total selected-edge estimate remains strict. The result therefore includes generalized states with zero angles and does not require the tetrahedron to be genuinely nondegenerate.")),
                    Paragraph(Text("This is an estimate for the specified original six-slot cosine and its clipped extension. Its use with actual geometric dihedral angles requires their identification with this formula and one common global length vector. The theorem supplies neither volume-maximizer existence, global face gluing, normal-link topology nor same-manifold geometric realization, and it does not settle unrestricted CFMP. The original cosine formula and generic square-root, inverse-cosine and finite-sum facts are reused; no literature priority is asserted."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application: a positive four-angle right inverse of the same extended-angle formula. The construction below applies the original rawCos and extendedAngle of TwoLengthAngleSum, with the original FourCycleCurvature.frame and FourCycleEnvelopes.rad, numerator and cosine. It gives positive length parameters whose six extended angles are prescribed by four angles in a strict domain. The scalar algebra is first given on its own domain, then its signs and its correspondence with all six original edge positions are established.")),
            Paragraph(Text("Let B₄ be the set of u=(ρ,ω,α,β) in ℝ⁴ such that ρ,ω,α,β>0, ρ+α+β<π and ω+α+β<π. All four angles lie in (0,π), as does α+β. For any real quadruple z=(r,o,a,b), define Jz=(r,a,b,o,a,b) in the original slot order (12,13,14,34,24,23), indexed by 0,1,2,3,4,5. On B₄ we will use z=cos u=(cos ρ,cos ω,cos α,cos β), with cosine taken componentwise. The coordinates r and o vary independently; the transverse coordinates a and b each occupy two slots.")),
            Paragraph(Text("Reduced scalar data. For a real quadruple z=(r,o,a,b), define the following polynomials; a symbol without its argument denotes its value at z. Set d=r²+a²+b²+2rab−1 and e=o²+a²+b²+2oab−1.")),
            Paragraph(Text("The axial numerators are N_r=2ab+r(a²+b²)−(r²−1)o and N_o=2ab+o(a²+b²)−(o²−1)r. The transverse numerators are N_a=b(r+o)+a(ro+b²−a²+1) and N_b=a(r+o)+b(ro+a²−b²+1).")),
            Paragraph(Text("Set L=(a+b)²−(r−1)(o−1), M=(r+1)(o+1)−(a−b)² and K=LM. Whenever d>0 and e>0, write s=√(de)>0 and define Tz=(N_r/d,N_o/e,N_a/s,N_b/s). Every square root here and below is the nonnegative real square root. We will show that d(Tz)>0, e(Tz)>0 and T(Tz)=z whenever d>0, e>0 and K≠0.")),
            Paragraph(Text("The six sum and difference laws. Direct expansion of the displayed polynomials gives d+N_r=(r+1)L, d−N_r=(r−1)M, e+N_o=(o+1)L, e−N_o=(o−1)M, N_a+N_b=(a+b)M and N_a−N_b=−(a−b)L. These identities hold for every real quadruple, before any positivity assumption.")),
            Paragraph(Text("Assume now d>0 and e>0, and write w=Tz=(r′,o′,a′,b′). Dividing those six identities by their respective nonzero denominators gives r′+1=(r+1)L/d, r′−1=(1−r)M/d, o′+1=(o+1)L/e, o′−1=(1−o)M/e, a′+b′=(a+b)M/s and a′−b′=−(a−b)L/s. The identity s²=de fixes the normalization in both transverse coordinates.")),
            Paragraph(Text("To transform L, substitute the sum law and the two axial difference laws into its definition: L(w)=(a′+b′)²−(r′−1)(o′−1)=M²[(a+b)²−(1−r)(1−o)]/(de)=LM²/(de). Here (1−r)(1−o)=(r−1)(o−1), so the bracket is precisely L.")),
            Paragraph(Text("Similarly, the axial sum laws and the transverse difference law give M(w)=(r′+1)(o′+1)−(a′−b′)²=L²[(r+1)(o+1)−(a−b)²]/(de)=L²M/(de). Thus both transformed factors are obtained from the same six laws, with no sign assumption on L, M, a or b.")),
            Paragraph(Text("To recover the second-pass data, put D=K²/(d²e), E=K²/(de²) and C=K²/(de s). Apply the six polynomial laws again, now at w. For example, d(w)+N_r(w)=(r′+1)L(w)=[(r+1)L/d][LM²/(de)]=(r+1)D, while d(w)−N_r(w)=(r′−1)M(w)=[(1−r)M/d][L²M/(de)]=(1−r)D.")),
            Paragraph(Text("The other four transformed laws are e(w)+N_o(w)=(o+1)E, e(w)−N_o(w)=(1−o)E, N_a(w)+N_b(w)=(a+b)C and N_a(w)−N_b(w)=(a−b)C. For the last identity, the two minus signs cancel: −(a′−b′)L(w)=−[−(a−b)L/s][LM²/(de)]=(a−b)C. The transverse sum similarly equals [(a+b)M/s][L²M/(de)].")),
            Paragraph(Text("Adding and subtracting each pair, then dividing by 2, yields d(w)=D, e(w)=E, N_r(w)=rD, N_o(w)=oE, N_a(w)=aC and N_b(w)=bC. In expanded form the transformed radicands are K²/(d²e) and K²/(de²); the transformed numerators are rK²/(d²e), oK²/(de²), aK²/(de√(de)) and bK²/(de√(de)), respectively.")),
            Paragraph(Text("If K≠0, then K²>0, and d,e,s>0 imply D,E,C>0. Moreover C²=K⁴/(d²e²s²)=K⁴/(d³e³)=DE=d(w)e(w). The positive square root is therefore √(d(w)e(w))=C=K²/(de√(de)). This identifies its sign as well as its square. Division now gives T(w)=(rD/D,oE/E,aC/C,bC/C)=z. In particular, the involution uses positive denominators even if N_a(w)=aC or N_b(w)=bC is negative.")),
            Paragraph(Text("The positive branch on B₄. We next derive all sign assumptions from the angle inequalities. For positive x,y,z with x+y+z<π, one has 0<sin y sin z<cos x+cos y cos z. Indeed, y,z lie in (0,π), so their sines are positive. Also 0<x<π−(y+z)<π; strict decrease of cosine on [0,π] gives cos x>cos(π−(y+z))=sin y sin z−cos y cos z. This is the triangle-gap inequality used below.")),
            Paragraph(Text("For u∈B₄ and z=cos u, put p=sin α sin β and t=p−ab. Then p>0, p²=(1−a²)(1−b²), and t=−cos(α+β)∈(−1,1). Each of r,o,a,b lies in (−1,1), and 1−a²=sin²α>0, 1−b²=sin²β>0. Applying the triangle-gap inequality to (ρ,α,β) and (ω,α,β) gives r+ab>p and o+ab>p, equivalently r>t and o>t.")),
            Paragraph(Text("The radicands factor as d=(r+ab−p)(r+ab+p) and e=(o+ab−p)(o+ab+p): expansion uses p²=(1−a²)(1−b²). Both factors in each product are positive, since r+ab>p>0 and o+ab>p>0. Hence d>0 and e>0, and s=√(de)>0.")),
            Paragraph(Text("The factors L and M have the decompositions L=(r−t)(1−o)+(o−t+2p)(1−t) and M=(r−t)(1+o)+(o−t+2p)(1+t). They follow by expansion from t=p−ab and p²=(1−a²)(1−b²). Every displayed factor is positive: r−t>0, o−t+2p>0, −1<o<1 and −1<t<1. Consequently L>0, M>0 and K=LM>0.")),
            Paragraph(Text("To control the transverse numerator signs, apply the triangle-gap inequality also to (β,α,ω) and (α,β,ω). Their sums equal ω+α+β<π, and they give b+ao>sin α sin ω>0 and a+bo>sin β sin ω>0. No positivity of a=cos α or b=cos β is required.")),
            Paragraph(Text("The useful numerator factorizations are N_a=(r+ab)(b+ao)+(1−a²)(a+bo) and N_b=(r+ab)(a+bo)+(1−b²)(b+ao). Direct expansion recovers the original N_a and N_b. Since r+ab>p>0 and all the other displayed factors are positive by the preceding inequalities, N_a>0 and N_b>0, including when either transverse angle is obtuse.")),
            Paragraph(Text("The squared gaps are N_a²−de=(1−a²)LM=(1−a²)K>0 and N_b²−de=(1−b²)LM=(1−b²)K>0. To pass from squared gaps to strict numerator bounds, factor N_a²−s²=(N_a−s)(N_a+s). Since N_a+s>0, the positive gap forces N_a−s>0. The identical argument with N_b gives N_b>s. Thus N_a/√(de)>1 and N_b/√(de)>1 with the positive square-root branch explicitly fixed.")),
            Paragraph(Text("For the axial coordinates, the difference laws give N_r−d=(1−r)M>0 and N_o−e=(1−o)M>0. Dividing by d>0 and e>0 proves N_r/d>1 and N_o/e>1. We have therefore derived d(z)>0, e(z)>0, K(z)>0 and every coordinate of Tz greater than 1 from exactly u∈B₄.")),
            Paragraph(Text("The length map and the original angle field. Define Ψ on B₄ componentwise by Ψ(u)=(arcosh(N_r/d),arcosh(N_o/e),arcosh(N_a/√(de)),arcosh(N_b/√(de))), where every scalar on the right is evaluated at z=cos u. Here arcosh is the real inverse hyperbolic cosine on [1,∞), with values in [0,∞). The strict bounds Tz>1 prove that all four coordinates of Ψ(u) are strictly positive.")),
            Paragraph(Text("For any real length quadruple q=(q_r,q_o,q_a,q_b), define the six-vector ℓ(q) by ℓ(q)_i=cosh(max((Jq)_i,0)) for i=0,…,5. The original extendedAngle receives this cosine-length vector. Define θ(q)=(extendedAngle(ℓ(q),0),extendedAngle(ℓ(q),3),extendedAngle(ℓ(q),1),extendedAngle(ℓ(q),2)), extracting axial slots 0,3 and transverse slots 1,2 in the order (ρ,ω,α,β). Thus θ uses the existing formula with its coordinatewise positive part, hyperbolic cosine and clamp.")),
            Paragraph(Text("The six native frames. For six frame entries (X,Y,Z,O,V,W), the reused numerator is YZ+VW+XYV+XZW−(X²−1)O. The reused radicand is rad(X,Y,Z)=2XYZ+X²+Y²+Z²−1. The original cosine divides that numerator first by √rad(X,Y,W) and then by √rad(X,Z,V). Applying the original frame to Jz gives the following entries and, in each case, the corresponding triple (numerator,left radicand,right radicand). The entries in this paragraph and the next are scalar cosine coordinates.")),
            Paragraph(Text("At slot 0 (edge 12), the frame reads (r,a,b,o,a,b), giving (N_r,d,d). At slot 1 (edge 13), it reads (a,b,r,a,b,o), giving (N_a,e,d). At slot 2 (edge 14), it reads (b,a,r,b,a,o), giving (N_b,e,d). At slot 3 (edge 34), it reads (o,a,b,r,a,b), giving (N_o,e,e). At slot 4 (edge 24), it reads (a,b,r,a,b,o), giving (N_a,e,d). At slot 5 (edge 23), it reads (b,a,r,b,a,o), giving (N_b,e,d). Thus the repeated transverse coordinates retain all four of their actual occurrences.")),
            Paragraph(Text("For d,e>0, the denominator products reduce as √d√d=d, √e√e=e and √e√d=√(de). Combining the six numerator and radicand triples therefore gives rawCos(Jz)=(N_r/d,N_a/√(de),N_b/√(de),N_o/e,N_a/√(de),N_b/√(de))=J(Tz). This identity holds for every real z with d(z)>0 and e(z)>0; it imposes no numerator sign condition.")),
            Paragraph(Text("Returning all six angles. Fix u∈B₄ and again let z=cos u and w=Tz. Every coordinate of Ψ(u) is positive, so max((JΨ(u))_i,0)=(JΨ(u))_i at every slot. Since each coordinate of w is greater than 1, cosh(arcosh w_j)=w_j for j=r,o,a,b. Consequently ℓ(Ψ(u))=Jw=J(Tz), with the positive part removed before applying this inverse-function identity.")),
            Paragraph(Text("The scalar involution supplies d(w)>0, e(w)>0 and T(w)=z. Applying the six-frame identity at w, rather than presupposing a second positive branch, yields rawCos(ℓ(Ψ(u)))=rawCos(Jw)=J(Tw)=Jz. At each slot i the last quantity is cos((Ju)_i). Even if a or b is negative, the second-pass numerators aC and bC are divided by the positive C and return those signed cosine coordinates.")),
            Paragraph(Text("For each i, −1≤cos((Ju)_i)≤1, so min(cos((Ju)_i),1)=cos((Ju)_i) and max(−1,cos((Ju)_i))=cos((Ju)_i). The clamp in the original extendedAngle is therefore inactive. Also 0<(Ju)_i<π by B₄, so arccos(cos((Ju)_i))=(Ju)_i on the principal interval [0,π]. It follows that extendedAngle(ℓ(Ψ(u)),i)=(Ju)_i for every i=0,…,5.")),
            Paragraph(Text("Explicitly, the six returned extended angles, in edge order (12,13,14,34,24,23), are (ρ,α,β,ω,α,β). The four selected outputs in slot order (0,3,1,2) are therefore θ(Ψ(u))=(ρ,ω,α,β)=u. The exact conclusion on B₄ is that Ψ maps to (0,∞)⁴, all six original extended-angle occurrences return Ju, and θ∘Ψ is the identity on B₄.")),
            Paragraph(Text("The application concerns the specified original angle formula on the four-coordinate family J(ℝ⁴), with the strict domain B₄ and the displayed positive length map. Identifying these formula values with geometric dihedral angles of a realized tetrahedron requires a separate geometric realization argument. A left inverse, uniqueness of a realizing length vector, boundary extension, an inverse for six independent coordinates, derivative or monotonicity assertions, and global gluing or existence conclusions lie outside the statement above.")),
            Paragraph(Text("Application: the occurrence-weighted directional derivative of the same four-coordinate field. Keep the six-slot map J, cosine-length vector ℓ(q), angle field θ(q), and scalar polynomials above. For q=(q_r,q_o,q_a,q_b) with four independent positive length coordinates, write z=cosh q componentwise. The analytic domain considered here consists exactly of q>0, L(z)>0 and M(z)>0. Calling this the genuine formula domain asserts these inequalities; identification with a geometric tetrahedron remains a separate obligation.")),
            Paragraph(Text("The occurrence-weighted field is f(q)=(θ_r(q),θ_o(q),2θ_a(q),2θ_b(q)). Thus h·f(q)=h_rθ_r(q)+h_oθ_o(q)+2h_aθ_a(q)+2h_bθ_b(q) for an arbitrary real direction h. The two factors of 2 count the two original occurrences of each transverse coordinate. All four entries of q and h vary independently, and no equality between the axial coordinates or transverse coordinates is imposed.")),
            Paragraph(Text("At z=cosh q with q>0, each scalar coordinate r,o,a,b is greater than 1. Consequently d,e>0. The polynomial discriminants are d²−N_r²=(r²−1)K, e²−N_o²=(o²−1)K, de−N_a²=(a²−1)K and de−N_b²=(b²−1)K. On the stated domain K=LM>0, so all four coordinates of Tz lie strictly between −1 and 1. The native six-frame identity therefore makes the clamp inactive at q.")),
            Paragraph(Text("For any fixed direction h, the four length coordinates and the two factors L(cosh(q+th)), M(cosh(q+th)) remain positive for t in a neighborhood of 0. On this neighborhood the original four-angle field θ equals arccos(T(cosh(q+th))) in the four selected slots. This local equality justifies differentiating the actual field; it introduces no differentiability premise for the clamped formula on a flat boundary.")),
            Paragraph(Text("Put u=θ(q)=(ρ,ω,α,β), c=(cos ρ,cos ω,cos α,cos β) and s=(sin ρ,sin ω,sin α,sin β). All four entries of u belong to (0,π). The exact native substitutions are c=Tz and s_r=sinh(q_r)√K/d, s_o=sinh(q_o)√K/e, s_a=sinh(q_a)√K/√(de), s_b=sinh(q_b)√K/√(de). These are positive square-root branches: sin(arccos x)=√(1−x²), the four discriminants above and sinh²t=cosh²t−1 give the identities, while q>0 makes each sinh positive.")),
            Paragraph(Text("Define p=s_a s_b, X=c_r+c_a c_b and Y=c_o+c_a c_b. For a direction h, the five-square expression is Q(q,h)=(X²−p²)h_r²+(Y²−p²)h_o²+(s_r h_r+s_o h_o−2s_a c_b h_a−2s_b c_a h_b)²+(X−p)(Y−p)(h_a+h_b)²+(X+p)(Y+p)(h_a−h_b)². Set κ(q)=de/(K√K), with every scalar on the right evaluated at z=cosh q.")),
            Paragraph(Text("The exact directional identity is (d/dt)|_{t=0}[h·f(q+th)]=κ(q)Q(q,h) on q>0, L(cosh q)>0 and M(cosh q)>0, for every real h. In particular, the left side differentiates the occurrence-weighted field extracted from the existing extendedAngle, rather than a separately chosen angle map.")),
            Paragraph(Text("To obtain the identity directly, differentiate z(t)=cosh(q+th), whose velocity at 0 is v_j=sinh(q_j)h_j. Differentiate each displayed polynomial d,e,N_r,N_o,N_a,N_b in this velocity. The common transverse denominator has derivative (ḋe+dė)/(2√(de)); the axial quotients have derivatives (Ṅ_r d−N_r ḋ)/d² and (Ṅ_o e−N_o ė)/e², and the transverse quotients use the same quotient rule. Composing with arccos multiplies each quotient derivative by −1/√(1−c_j²). Sum the four results with coefficients h_r,h_o,2h_a,2h_b.")),
            Paragraph(Text("For the final scalar reduction, replace the four square roots √(1−c_j²) by the positive sine formulas and use (√K)²=K, (√(de))²=de and sinh²(q_j)=z_j²−1. After clearing the positive denominators, expansion of the polynomial numerators gives the five-square expression above with the factor de/(K√K). This calculation retains both independent axial velocities and both repeated transverse contributions. It uses neither a six-variable Jacobian theorem nor a potential whose gradient is assumed to be f.")),
            Paragraph(Text("The derivative identity is a local statement on the stated genuine formula domain. Its use for nonnegative derivatives requires the signs of the five-square coefficients; a monotonicity conclusion across flat blocks additionally requires continuity and a justified treatment of exceptional outputs. It supplies no derivative at a flat block, boundary extension, common global length vector, global gluing, uniqueness or same-manifold realization.")))));

    private static Formula Statement()
    {
        var A = F.Id("A"); var B = F.Id("B"); var S = F.Id("S");
        var count = Call("card", S);
        var premises = And(Lt(F.D(1), A),
            Lt(Call("add", Call("mul", F.D(4), A), F.D(5)), B),
            Le(F.D(2), count));
        var bound = Call("div", Call("mul", count, F.Id("pi")), F.D(4));
        return All([("A", F.Id("Real")), ("B", F.Id("Real")),
            ("S", Call("Finset", Call("Fin", F.D(6))))],
            Imp(premises, Lt(bound, Call("AngleSum", A, B, S))));
    }

    private static Formula RadicandStatement()
    {
        var x=F.Id("x");var y=F.Id("y");var z=F.Id("z");
        return All([("x",F.Id("Real")),("y",F.Id("Real")),("z",F.Id("Real"))],
            Imp(And(Lt(F.D(1),x),Lt(F.D(1),y),Lt(F.D(1),z)),Lt(F.D(0),Call("rad",x,y,z))));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..variables.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
}
