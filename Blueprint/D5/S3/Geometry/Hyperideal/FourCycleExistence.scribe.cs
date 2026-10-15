using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every four-cycle incidence system has one shared interior zero-curvature vector.",
        H("A simultaneous solution for all global edge equations"),
        Blocks(
            Paragraph(Text("Let T be a finite type of tetrahedra and E a type of global edge labels "
                + "with decidable equality. The incidence s assigns a label to each of the six local "
                + "edges of every tetrahedron and a low/high colour to each global label. "
                + "FourCycle(s) requires the four low slots to form the prescribed local cycle, "
                + "degree eight at each low label, and degree at least twelve at each high label. "
                + "Degrees are actual fibre cardinalities, including repeated occurrences.")),
            Paragraph(Text("The lower and upper endpoints L(s) and U(s), local cosine C(s,x,o), "
                + "and curvature K(s,x,e) are exactly those of FourCycleCurvature. "
                + "In particular, each local coordinate reads the same global vector x:E -> Real. "
                + "K is 2pi minus the sum of arccos(C) over the actual occurrence fibre.")),
            Describe.Lean(
                DescribeId.Create("fourcycle-shared-zero-curvature"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature"),
                H("An interior vector with all angle sums equal to 2pi"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every global label has a nonempty finite occurrence fibre, "
                        + "so the incidence map is surjective and the edge-label type is finite. "
                        + "This finiteness is derived from FourCycle(s); it is not an additional hypothesis.")),
                    Paragraph(Text("The established box has strictly positive radicands, "
                        + "strictly admissible cosines, and inward curvature margins on all faces. "
                        + "Polynomial operations, square roots away from zero, division and arccos "
                        + "make the actual shared curvature map continuous on this box.")),
                    Paragraph(Text("Normalize the box to a unit cube. The cube is a retract of "
                        + "a simplex: divide its n coordinates by n+1, append the slack coordinate "
                        + "one minus their sum, and project back by multiplying the n non-slack weights "
                        + "by n+1 and clamping to [0,1]. The classical simplex fixed-point theorem "
                        + "therefore applies to the clamped curvature self-map. Strict face signs "
                        + "exclude every boundary coordinate of its fixed point; interior clamp "
                        + "cancellation then forces every curvature to vanish.")),
                    Paragraph(Text("The conclusion concerns the real incidence system. "
                        + "It does not assert that arbitrary incidence data form a manifold, "
                        + "supply face pairings or vertex-link conditions, or prove unrestricted CFMP. "
                        + "The geometric interpretation of the cosine formula and the passage to "
                        + "a complete hyperbolic realization retain their separate hypotheses."))),
                DescribeRole.Theorem),
            Paragraph(Text("The same four-cycle box also permits an arbitrary prescribed raw "
                + "curvature vector kappa:E -> Real with |kappa(e)|<eta for every global label, "
                + "where eta is the exact positive FourCycleCurvature.margin. The incidence, "
                + "colouring, fibre degrees, endpoints L(s), U(s), and occurrence-counted "
                + "curvature K(s,x,e) are unchanged. Finiteness of E follows from the actual "
                + "positive fibre degrees as above; no independent finite-edge or solution "
                + "assumption is added.")),
            Paragraph(Text("For normalized cube coordinates u, use the same affine box map "
                + "X(u)_e=L(s,e)+(U(s,e)-L(s,e))*u_e and clamp the increment "
                + "u_e+K(s,X(u),e)-kappa(e) to [0,1]. Positive radicands and nonzero "
                + "denominators, polynomial and square-root continuity, continuous arccos, "
                + "finite occurrence sums, and the continuous min/max clamp make this map "
                + "continuous. On a lower face, "
                + "K-kappa>=eta-kappa(e)>0; on an upper face, "
                + "K-kappa<=-eta-kappa(e)<0. The two strict inequalities use the two sides "
                + "of |kappa(e)|<eta. The existing cube fixed-point and clamp arguments "
                + "therefore exclude every boundary coordinate and give K(s,X(u),e)=kappa(e) "
                + "for every global label at one shared fixed point.")),
            Paragraph(Text("Consequently one shared vector x lies strictly between the original "
                + "lower and upper endpoints at every global label, every original local "
                + "cosine remains strictly between -1 and 1, and every raw curvature equals "
                + "its prescribed component. Repeated occurrences and repeated labels still "
                + "read that same x. The admissible curvature bound eta is independent of "
                + "the number of tetrahedra, while the original high-edge lower floor can "
                + "depend on that number; this does not supply a uniform spectral bound.")),
            Paragraph(Text("This is an application of the established analytic box and "
                + "fixed-point machinery. Identifying x with cosh of native edge lengths, "
                + "identifying the raw angle with the native dihedral angle, constructing "
                + "paired face isometries, and proving edge and truncation-endpoint cone "
                + "charts retain their separate geometric obligations. A nonzero prescribed "
                + "raw defect is not by itself a constructed native cone metric.")),
            Paragraph(Text("For a finite nonempty block set T and a finite global label set E, "
                + "let Q(t,i), i in Fin 4, read four coordinates from one vector ell:E -> Real. "
                + "The native six local occurrences have labels "
                + "[Q(t,0),Q(t,2),Q(t,3),Q(t,1),Q(t,2),Q(t,3)]. "
                + "Assume this actual six-occurrence map is surjective. Repeated labels remain "
                + "separate occurrences. With local coordinates ordered [r,o,a,b], the native "
                + "angle field is Phi=[theta_r,theta_o,2 theta_a,2 theta_b]; the factors two "
                + "account for the repeated transverse occurrences.")),
            Paragraph(Text("Choose an initial native angle quadruple u_t satisfying strict B4 "
                + "for every block: all four entries are positive, u_r+u_a+u_b<pi, and "
                + "u_o+u_a+u_b<pi. Write b_t=[u_r,u_o,2u_a,2u_b]. "
                + "The positive native right inverse supplies local comparison lengths for "
                + "these targets. These comparison lengths belong to individual blocks; "
                + "their existence imposes no simultaneous global length assignment.")),
            Paragraph(Text("Let m_t be the minimum of the four positive entries and the two "
                + "positive B4 triangle margins, and take eps=(min_t m_t)/4. This one eps "
                + "is positive for the finite nonempty family. Perturb each weighted target "
                + "coordinate by plus or minus eps. In the native angle quadruple, a transverse "
                + "coordinate changes by half that amount. All eight perturbations remain in "
                + "strict B4. Applying the native right inverse gives nonnegative local vectors "
                + "Y(t,i,s) with Phi(Y(t,i,s))=b_t plus or minus eps times the i-th coordinate vector.")),
            Paragraph(Text("For all x,y in Real^4, (Phi(x)-Phi(y)) dot (x-y)>=0. "
                + "The native field is componentwise nonnegative and vanishes in its own coordinate whenever "
                + "that length coordinate is nonpositive. For each block, bound all eight "
                + "comparison dot-products by C_t=sum_(i,s)|Phi(Y(t,i,s)) dot Y(t,i,s)|. "
                + "The finite-witness estimate then gives eps times the local sup norm, "
                + "minus C_t, as a lower bound for (Phi(x)-b_t) dot x.")),
            Paragraph(Text("Define F(ell)_e by summing Phi(readout_Q(ell,t))_i-b_(t,i) "
                + "over every local position with Q(t,i)=e. Every summand reads the same ell. "
                + "Surjectivity ensures every global coordinate occurs in a block, so its "
                + "sup norm is at most the sum of the local readout norms. Finite-sum "
                + "reindexing gives F(ell) dot ell=sum_t (Phi(readout_Q(ell,t))-b_t) dot "
                + "readout_Q(ell,t), and consequently eps norm(ell)-C <= F(ell) dot ell "
                + "with C=sum_t C_t. Independent comparison witnesses are used only in this estimate.")),
            Paragraph(Text("The field F is continuous. Suppose it has no zero and put "
                + "R=C/eps+1. Normalize the cube [-R,R]^E to [0,1]^E and use the "
                + "self-map G_j=(1-F(ell)_j/norm(F(ell)))/2. The coordinate norm bound "
                + "puts G in the cube, and the assumed absence of zeros makes it continuous. "
                + "The same existing cube fixed-point supplier yields a point with "
                + "ell=-(R/norm(F(ell)))F(ell). Hence norm(ell)=R and F(ell) dot ell<=0, "
                + "whereas the outward estimate gives F(ell) dot ell>=eps R-C=eps>0. "
                + "This contradiction supplies one common zero of F.")),
            Paragraph(Text("Every target mass at a global label is strictly positive: "
                + "surjectivity supplies an actual occurrence and strict B4 supplies its "
                + "positive target. If ell_e<=0, each matching native field coordinate "
                + "vanishes, so F(ell)_e is minus this positive target mass. A zero of F "
                + "therefore has all global lengths strictly positive.")),
            Paragraph(Text("For the reciprocal-degree choice u_(t,i)=2pi/degree(Q(t,i)), "
                + "degree counts the original six-occurrence fibre. Summing its target "
                + "over that fibre gives exactly 2pi, with the two transverse repetitions "
                + "already present in Phi and b. At the common zero, the actual six-slot "
                + "extended native angle sum at every global label is consequently 2pi. "
                + "This specialization still requires strict B4 of every initial quadruple.")),
            Paragraph(Text("The reciprocal-degree specialization admits the following conditional "
                + "degree criterion. Put n=card T, m=card E, and let d(e) be the cardinality "
                + "of the fibre of e in the actual map T x Fin 6 -> E with labels "
                + "[Q(t,0),Q(t,2),Q(t,3),Q(t,1),Q(t,2),Q(t,3)]. Each pair (t,j) is "
                + "counted separately, including repeated labels within one block. Assume "
                + "this map is surjective, Q(t,2)=A and Q(t,3)=B for every t, and that "
                + "A, B, S are three pairwise distinct labels in E. Assume also m<n. "
                + "The two degree criteria below concern every label other than A and B.")),
            Paragraph(Text("Number the six occurrence slots from 0 to 5. The maps from "
                + "T x Fin 2 selecting slots 1 and 4 inject into the fibre of A; selecting "
                + "slots 2 and 5 gives an injection into the fibre of B. In each case, "
                + "equality of occurrence pairs recovers both the block and the selected slot. "
                + "Thus d(A)>=2n and d(B)>=2n, even when an axial slot also has label A or B. "
                + "The fibres over all labels partition T x Fin 6, so sum_(e in E) d(e)=6n. "
                + "Surjectivity makes every d(e) strictly positive.")),
            Paragraph(Text("The distinct labels A, B, S give 3<=m, and m<n therefore gives "
                + "n>=4. For either axial label e=Q(t,0) or e=Q(t,1), define the normalized "
                + "triangle budget R(e)=2/d(e)+2/d(A)+2/d(B). The common-label bounds "
                + "give 2/d(A)<=1/n and 2/d(B)<=1/n. If e is A or B, the axial term "
                + "is bounded by 1/n as well; its repeated appearance in R(e) remains "
                + "a separate term.")),
            Paragraph(Text("First assume d(e)>=4 for every e distinct from A and B. "
                + "When n>=5 and the axial label is A or B, R(e)<=3/n<=3/5<1. "
                + "For any other axial label, 2/d(e)<=1/2, so "
                + "R(e)<=1/2+2/n<=9/10<1. These estimates apply separately to both "
                + "Q(t,0) and Q(t,1).")),
            Paragraph(Text("For the remaining four-degree case n=4, the inequalities "
                + "3<=m<n force m=3. Hence A, B, S exhaust E, and the literal degree "
                + "mass becomes d(S)+d(A)+d(B)=24. The assumptions and injections give "
                + "d(S)>=4, d(A)>=8 and d(B)>=8. For an axial label S, these bounds give "
                + "R(S)<=1/2+1/4+1/4=1. Equality would force equality in all three "
                + "positive reciprocal bounds, hence d(S)=4, d(A)=8 and d(B)=8; their "
                + "sum would be 20, contradicting 24. Thus R(S)<1. If the axial label "
                + "is A or B, R(e)<=3/4<1. Exhaustion by the three labels covers both "
                + "axial slots, completing the four-degree criterion for every n>=4.")),
            Paragraph(Text("Independently, assume d(e)>=6 for every e distinct from A "
                + "and B. The same cardinality premise gives n>=4. For an axial label "
                + "A or B, R(e)<=3/n<=3/4<1; for any other axial label, "
                + "R(e)<=1/3+2/n<=5/6<1. This six-degree argument applies directly "
                + "to both axial slots for all n>=4, using no four-block endpoint "
                + "or three-label mass calculation.")),
            Paragraph(Text("Under either degree criterion, set u_(t,i)=2pi/d(Q(t,i)). "
                + "Surjectivity and pi>0 make all four entries positive. Multiplying "
                + "R(Q(t,0))<1 and R(Q(t,1))<1 by positive pi gives, respectively, "
                + "u_r+u_a+u_b<pi and u_o+u_a+u_b<pi, since Q(t,2)=A and Q(t,3)=B. "
                + "Thus every initial quadruple satisfies the strict B4 condition "
                + "required by the preceding common-length argument.")),
            Paragraph(Text("That argument supplies one global vector ell:E -> Real "
                + "with every ell_e>0 and F(ell)=0. Each occurrence in the fibre of e "
                + "has assigned target angle 2pi/d(e); its target sum is therefore "
                + "d(e) times 2pi/d(e)=2pi. The repeated transverse slots are exactly "
                + "the factors two in Phi and b. At F(ell)=0, the actual six-occurrence "
                + "extended native angle sum equals this assigned sum at every global "
                + "label. All these equalities use the same global vector ell.")),
            Paragraph(Text("These are conditional applications of the preceding "
                + "existence argument. The source cardinality inequality card E<card T "
                + "and the stated degree bounds remain premises; their extraction from "
                + "the original boundary Euler/genus assumptions is a separate obligation. "
                + "Applying the criteria to the original CFMP data also requires identifying "
                + "Q and its six-occurrence map with the actual face-pairing quotient, "
                + "including coverage and the three distinct labels. The genuine-angle "
                + "region, flat-block geometry and compatible complete hyperbolic gluing "
                + "retain their original geometric requirements.")),
            Paragraph(Text("This derivation applies the existing fixed-point machinery and "
                + "native analytic formulas under explicit hypotheses. It does not derive "
                + "the initial strict B4 condition from the original boundary Euler/genus "
                + "assumptions, identify arbitrary incidence data with the original face "
                + "quotient, or construct flat-block geometry and compatible hyperbolic gluing. "
                + "Strictly positive lengths alone do not establish that every block lies in the genuine-angle region. "
                + "Those geometric bridges are separate obligations of the original CFMP problem.")))));

    private static Formula Statement()
    {
        var t=F.Id("T"); var eType=F.Id("E"); var s=F.Id("s");
        var x=F.Id("x"); var e=F.Id("e"); var o=F.Id("o");
        var interior=All([("e",eType)],And(
            Lt(Apply(Call("L",s),e),Apply(x,e)),
            Lt(Apply(x,e),Apply(Call("U",s),e))));
        var cosine=Call("C",s,x,o);
        var strict=All([("o",Call("Product",t,Call("Fin",F.D(6))))],And(
            Lt(F.Seq(F.Minus,F.D(1)),cosine),Lt(cosine,F.D(1))));
        var zero=All([("e",eType)],Eq(Call("K",s,x,e),F.D(0)));
        var exists=new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"),
                new Formula.TypeArrow(eType,F.Id("Real")))],And(interior,strict,zero));
        return All([("T",F.Id("Type")),("E",F.Id("Type")),
            ("s",Call("Incidence",t,eType))],
            Imp(And(Call("Fintype",t),Call("DecidableEq",eType),Call("FourCycle",s)),exists));
    }

    private static Formula All((string Name,Formula Type)[] variables,Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var q=p[^1]; for(var i=p.Length-2;i>=0;i--) q=new Formula.Logic(p[i],FormulaLogicOperator.And,q);
        return q;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Apply(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula Call(string name,params Formula[] args)=>Apply(F.Id(name),args);
}
