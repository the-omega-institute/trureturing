using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;
internal sealed class OriginalReferenceRepeatedMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Mode balance and completeness for native repeated quantum outputs.",
        H("Loss is the decrease of the surviving mode weight"),Blocks(
            Describe.Lean(DescribeId.Create("native-mode-balance"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.native_mode_balance"),
                H("Every original control and every subinterval"),
                StatementSource.FromAuthor(Disp(Balance())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Fix c<1/2, 0<a<c and an original height k on [0,T] with constant phase zero. For each original mode i, let p_i(k) be its positive double-wall probability, S(t)=exp(-integral_0^t hazard(c,k)) its native survival, and f_i(t) the squared literal jump amplitude. For every 0<=s<=t<=T, f_i is integrable on (s,t] and its integral equals [S(s)p_i(k(s))-S(t)p_i(k(t))]/p_i(a). No initial-height equality is needed for this general balance law.")),
                    Paragraph(Text("The original regularity alternatives imply absolute continuity of k. The integrable native hazard has an absolutely continuous primitive. Exponentiation preserves absolute continuity on its compact range, and multiplication by each affine probability coordinate preserves it. Almost everywhere, logarithmic differentiation gives g_i=hazard-p_i'/p_i. The explicit five coordinates show g_i>=0. Consequently the literal squared square-root amplitude is g_i S p_i/p_i(a), which is minus the derivative of S p_i divided by p_i(a). The fundamental theorem for absolutely continuous functions gives the balance identity. Exceptional derivative values at corners have zero Lebesgue mass."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("repeated-reference-completeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_completeness"),
                H("The same arbitrary joint input across prefix and suffix"),
                StatementSource.FromAuthor(Disp(Completeness())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Let B be any band 0<a<b<c<1/2, n>=1 and e either literal early or late history k. Put q=(a/b)(c-b)/(c-a). H is any complete complex Hilbert space, including nonseparable spaces. rho is any positive trace-class operator on Blocks(Fin5,H), with no normalization, finite-rank, separability or product-state assumption. A_i is the positive trace-class compression of that same rho to reference block i. The actual reference-output density is F_i(t)=f_i(t) A_i, as identified with tensor-amplified Kraus conjugation by OriginalReferenceOutputMeasure.repeated_failure_event.")),
                    Paragraph(Text("For every mode i and every 1<t<=2, F_i(t)=q^n F_i^suffix(t-1), where the suffix uses the same rho and the original earlySuffix or lateSuffix control. This is exact prefix scaling of each reference operator, using the already established chronological Kraus action. The coefficient integrals on (0,1], (1,2] and (0,2] are respectively 1-q^n, q^n(1-q) and 1-q^(n+1). In particular the suffix Bochner integral is q^n(1-q) A_i. The endpoint heights and native survival values are supplied by OriginalRepeatedPrefix; they are applied to the general mode balance identity.")),
                    Paragraph(Text("Summing the norms of the five suffix event outputs gives q^n(1-q) norm(rho). Summing the norms of the five full failure event outputs and adding norm(q^(n+1) rho) gives norm(rho). Positivity turns each scalar multiple into its nonnegative coefficient times norm(A_i), and the same-input block trace partition gives sum_i norm(A_i)=norm(rho). Thus all modes and their unchanged reference correlations contribute to exact mass completeness. The terminal term here is the scalar successful endpoint action. The result does not claim the operational supremum or a distance formula for general initially stopped six-coordinate inputs.")),
                    Paragraph(Text("The operational supremum, general live-stopped coherences and the inverse/resource applications require further statements. The present identities retain their unnormalized form; normalized live inputs have norm(rho)=1."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("repeated-reference-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_distance"),
                H("Common prefix cancellation and disjoint suffix windows"),
                StatementSource.FromAuthor(Disp(Distance())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("For every band B, n>=1, arbitrary complete complex Hilbert reference H and positive joint trace-class rho, every mode's prefix Bochner outputs agree on (0,1] intersect every Borel event E. Moreover sum_i integral_(0,2] norm(F_i^early(t)-F_i^late(t)) equals 2 q^n(1-q) norm(rho). Both densities use the same rho, including all entanglement with its unchanged reference.")),
                    Paragraph(Text("Before time one, the literal heights, native survival and jump rates coincide almost everywhere. The seam has zero Lebesgue mass, giving equality on every restricted event. The late suffix is constant before its excursion and the early suffix is constant after its excursion. Local constancy makes both the height derivative and logarithmic probability derivative vanish, so the actual jump coefficient vanishes on the corresponding waiting window. Exact prefix scaling carries these zero densities to the original clock. Except at the middle seam, one of the two suffix densities is zero. Thus the norm of their difference equals the sum of their norms, without comparing independent inputs or replacing joint operators by marginal probabilities.")),
                    Paragraph(Text("Split the full interval into prefix and suffix. The prefix difference integrates to zero, and the suffix norm integral is the sum of the two positive suffix masses. The preceding completeness theorem supplies each mass q^n(1-q) norm(rho). For normalized live rho, the half-sum convention therefore gives q^n(1-q) for this failure-density contribution. This theorem does not itself define an operational supremum, prove the general six-coordinate initial-state extension, or close the inverse and resource statements."))),DescribeRole.Theorem))));
    private static Formula Balance()
    {
        Formula c=F.Id("c"),a=F.Id("a"),t=F.Id("t"),s=F.Id("s"),k=F.Id("k"),i=F.Id("i"),cap=F.Id("T");
        Formula density=C("modeCoefficient",c,a,k,i);
        Formula mass=Div(Sub(Mul(C("survival",c,k,s),C("p",c,C("apply",k,s),i)),Mul(C("survival",c,k,t),C("p",c,C("apply",k,t),i))),C("p",c,a,i));
        Formula assumptions=And(C("lt",c,Div(D(1),D(2))),And(C("memIoo",a,D(0),c),And(C("OriginalConstantPhaseControl",c,cap,k),C("orderedSubinterval",s,t,D(0),cap))));
        return All([V("c",R),V("a",R),V("T",R),V("k",C("Function",R,R)),V("i",C("Fin",D(5))),V("s",R),V("t",R)],Imp(assumptions,And(C("IntegrableOn",density,C("Ioc",s,t)),Eq(C("integral",density,C("Ioc",s,t)),mass))));
    }
    private static Formula Completeness()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),rho=F.Id("rho"),i=F.Id("i"),t=F.Id("t"),q=C("q",b);
        Formula k=C("literalEarlyLate",b,n,e),suffix=C("literalSuffix",b,e),qn=Pow(q,n),qnext=Pow(q,Add(n,D(1))),mass=Mul(qn,Sub(D(1),q));
        Formula density=C("modeCoefficient",b,k,i),output=C("modeOutput",b,k,i,rho),ai=C("referenceCompression",rho,i);
        Formula scaling=All([V("t",R)],Imp(C("memIoc",t,D(1),D(2)),Eq(C("apply",output,t),C("smul",qn,C("apply",C("modeOutput",b,suffix,i,rho),Sub(t,D(1)))))));
        Formula modes=All([V("i",C("Fin",D(5)))],And(scaling,And(Eq(C("integral",density,C("Ioc",D(0),D(1))),Sub(D(1),qn)),And(Eq(C("integral",density,C("Ioc",D(1),D(2))),mass),And(Eq(C("integral",density,C("Ioc",D(0),D(2))),Sub(D(1),qnext)),Eq(C("integral",output,C("Ioc",D(1),D(2))),C("smul",mass,ai)))))));
        Formula sumSuffix=C("sumModeOutputIntegralNorms",b,k,rho,C("Ioc",D(1),D(2)));
        Formula sumFull=C("sumModeOutputIntegralNorms",b,k,rho,C("Ioc",D(0),D(2)));
        Formula body=And(modes,And(Eq(sumSuffix,Mul(mass,C("norm",rho))),Eq(Add(sumFull,C("norm",C("smul",qnext,rho))),C("norm",rho))));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("e",F.Id("Bool")),V("rho",C("PositiveJointTraceClass",F.Id("H")))],Imp(C("atLeastOne",n),body));
    }
    private static Formula Distance()
    {
        Formula b=F.Id("B"),n=F.Id("n"),rho=F.Id("rho"),i=F.Id("i"),ev=F.Id("E"),q=C("q",b);
        Formula early=C("literalEarly",b,n),late=C("literalLate",b,n);
        Formula fe=C("modeOutput",b,early,i,rho),fl=C("modeOutput",b,late,i,rho);
        Formula domain=C("intersection",C("Ioc",D(0),D(1)),ev);
        Formula prefix=All([V("i",C("Fin",D(5))),V("E",C("Set",R))],Imp(C("MeasurableSet",ev),Eq(C("integral",fe,domain),C("integral",fl,domain))));
        Formula distance=C("sumModesIntegralNormDifference",b,early,late,rho,C("Ioc",D(0),D(2)));
        Formula mass=Mul(Mul(D(2),Mul(Pow(q,n),Sub(D(1),q))),C("norm",rho));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("rho",C("PositiveJointTraceClass",F.Id("H")))],Imp(C("atLeastOne",n),And(prefix,Eq(distance,mass))));
    }
    private static Formula Sub(Formula a,Formula b)=>Subtract(a,b);
    private static Formula Mul(Formula a,Formula b)=>Multiply(a,b);
    private static Formula Div(Formula a,Formula b)=>C("divide",a,b);
    private static Formula Pow(Formula a,Formula b)=>C("power",a,b);
    private static readonly Formula R=F.Id("Real");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string n,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(n),[..xs]);
}
