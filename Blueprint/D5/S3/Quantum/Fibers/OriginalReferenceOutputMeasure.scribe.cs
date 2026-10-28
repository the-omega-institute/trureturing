using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;
internal sealed class OriginalReferenceOutputMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Trace-norm Bochner outputs for the literal repeated early/late controls.",
        H("Every reference and every Borel time event"),Blocks(
            Describe.Lean(DescribeId.Create("repeated-failure-event"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceOutputMeasure.repeated_failure_event"),
                H("Positive actual quantum failure outputs on the complete time domain"),
                StatementSource.FromAuthor(Disp(Statement())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Fix a band 0<a<b<c<1/2, any integer n>=1, either literal early or late history k, and any of its five original modes i. H is an arbitrary complete complex Hilbert space, with no separability or dimension restriction. rho is any positive trace-class operator on the full five-coordinate Hilbert sum B(Fin5,H), without normalization, rank, or product-state restrictions. The finite-system tensor isometry and the original amplified row are supplied by FiniteBlocks and OriginalReferenceLegOutput.")),
                    Paragraph(Text("Let alpha_i(t)=sqrt(g_i(t))*sqrt(S(t))*sqrt(p_i(k(t))/p_i(a)), using the actual original totalized derivatives, hazard integral and Kraus matrices. Set f_i(t)=normSq(alpha_i(t)), A_i=pi_i rho iota_i, and F_i(t)=f_i(t) A_i in the genuine trace-norm Banach space TraceClass H. At every real time its underlying operator is exactly J_i(t) rho J_i(t)*. In particular, the time values at corners are not substituted by assumed rate identities. Positivity and trace class of A_i come from compression of the same joint input; its reference correlations are retained.")),
                    Paragraph(Text("Continuity of the actual control on its time domain, measurability of derivatives, and continuity of the integrable hazard primitive give strong measurability of f_i on (0,2]. To prove integrability, evaluate the already established native marked probability law at one auxiliary source-family input. Its i-th density is exactly p_i(a) f_i(t), and its finite mode measure is bounded by the total probability measure. Dividing by the strictly positive p_i(a) proves integrability of f_i. This auxiliary scalar calculation does not restrict the quantum input rho: the resulting theorem quantifies over every positive joint input independently of that source-family witness.")),
                    Paragraph(Text("For every Borel E, let D=(0,2] intersect E. Both F_i on the full time domain and its restriction to D are Bochner integrable in trace norm. Its event integral equals (integral_D f_i) A_i, is positive, and satisfies norm(integral_D F_i)=integral_D norm(F_i). Scalar factorization keeps the range inside one fixed trace-class line, so nonseparable references require no countable basis assumption. The theorem retains each exact time event and original mode.")),
                    Paragraph(Text("This result supplies actual output identities, integrability and positive event integrals for the original repeated histories. It does not identify each suffix coefficient integral with q^n(1-q), prove the disjoint-window distance calculation, establish the operational supremum, extend a general initially stopped input, or supply the operational inverse/resource consumer. The mixed parent theorem and corollary remain open."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        Formula h=F.Id("H"), b=F.Id("B"), n=F.Id("n"), e=F.Id("e"), i=F.Id("i"), rho=F.Id("rho"), ev=F.Id("E");
        Formula k=C("literalEarlyLate",b,n,e), output=C("modeOutput",b,k,i,rho);
        Formula domain=C("intersection",C("Ioc",D(0),D(2)),ev);
        Formula integral=C("integralOnEvent",output,domain);
        Formula identity=Eq(integral,C("smul",C("integralOnEvent",C("modeCoefficient",b,k,i),domain),C("referenceCompression",rho,i)));
        Formula events=All([V("E",C("Set",R))],Imp(C("MeasurableSet",ev),And(C("IntegrableOnTraceNorm",output,domain),And(C("Positive",integral),And(identity,Eq(C("norm",integral),C("integralOnEvent",C("normFunction",output),domain)))))));
        Formula body=And(C("pointwiseActualKrausConjugationAllTimes",output,b,k,i,rho),And(C("IntegrableOnTraceNorm",output,C("Ioc",D(0),D(2))),events));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("e",F.Id("Bool")),V("i",C("Fin",D(5))),V("rho",C("TraceClass",C("Blocks",C("Fin",D(5)),h)))],Imp(And(C("atLeastOne",n),C("Positive",rho)),body));
    }
    private static readonly Formula R=F.Id("Real");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string name,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..xs]);
}
