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
