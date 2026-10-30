using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;
internal sealed class OriginalReferenceKrausDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Original absorbing Kraus rows retain arbitrary reference correlations.",
        H("Original jump outputs with a reference"),Blocks(
            Item("actual_raw_jump_operator","The literal amplitude includes every time value",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("c",R),V("a",R),V("k",R),V("S",R),V("g",C("Functions",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("rho",C("End",C("B",C("Fin",D(5)),F.Id("H"))))],
                    Equal(C("conjugate",J(),Rho),C("smul",C("normSq",C("amplitude",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I)),C("compression",Rho,I)))),
                "The literal absorbing row is alpha_i times coordinate i for every real parameter value. Its conjugation is normSq(alpha_i) times the same input compression, without a sign or differentiability assumption. This includes the totalized derivative values at finitely many control corners. On the nonnegative-rate domain the following theorem identifies the squared amplitude with the original rate coefficient. The repeated-control Bochner theorem consumes this exact operator identity, so it does not assume a desired output law or omit endpoint values."),
            Item("actual_jump_operator","The actual row selects the same input block",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("c",R),V("a",R),V("k",R),V("S",R),V("g",C("Functions",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("rho",C("End",C("B",C("Fin",D(5)),F.Id("H"))))],
                    Imp(Hyp(),Equal(C("conjugate",J(),Rho),C("smul",Coeff(),C("compression",Rho,I))))),
                "Let H be an arbitrary complete complex Hilbert reference and let B(Fin5,H)=PiLp 2 with five copies of H. The finite tensor coordinates identify this with the finite live system tensored with the unchanged reference. referenceJump is the sum over j of the actual original jumpKraus(c,a,k,S,g,i)[0,j] times the bounded coordinate projection pi_j. The row is derived from absorbingRow times successfulKraus, rather than prescribed by a desired output law. It equals alpha_i pi_i, where alpha_i=sqrt(g_i)*sqrt(S)*sqrt(p_i(k)/p_i(a)). For c<1/2, 0<a,k<c, S>=0 and g_i>=0, alpha_i times its complex conjugate equals f_i=g_i*S*p_i(k)/p_i(a). Expanding the actual conjugation gives J_i rho J_i*=f_i*pi_i rho iota_i, for the same arbitrary joint operator rho. No diagonal, finite-rank, pure, or product-state restriction is made."),
            Item("actual_jump_trace_norm","The genuine trace norm of the retained reference output",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("c",R),V("a",R),V("k",R),V("S",R),V("g",C("Functions",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("rho",C("TraceClass",C("B",C("Fin",D(5)),F.Id("H"))))],
                    Imp(Conj(Hyp(),Le(D(0),C("operator",Rho))),Conj(Equal(C("operator",Out()),C("conjugate",J(),C("operator",Rho))),Equal(C("norm",Out()),C("multiply",Coeff(),C("Re",C("trace",C("compression",C("operator",Rho),I)))))))),
                "For every positive trace-class joint rho, the heterogeneous positive compression theorem makes pi_i rho iota_i a genuine TraceClass H element. failureOutput is f_i times this element in its trace-norm Banach space. The preceding operator identity proves that its underlying operator is exactly the original amplified Kraus output. Positivity gives norm(pi_i rho iota_i)=Re Tr(pi_i rho iota_i); scalar homogeneity then gives the displayed norm. This statement is pointwise in time. It imposes no normalization assumption, and applies in particular to every normalized entangled input. The whole repeated-pair result additionally requires the actual time integrals, disjoint suffix supports, operational supremum, and the six-dimensional terminal block calculation."),
            Item("absorbing_jump_trace_norm","The absorbing successor preserves the reference norm",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("c",R),V("a",R),V("k",R),V("S",R),V("g",C("Functions",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("rho",C("TraceClass",C("B",C("Fin",D(5)),F.Id("H"))))],
                    Imp(Conj(Hyp(),Le(D(0),C("operator",Rho))),Conj(Equal(C("operator",C("absorbingFailureOutput",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I,Rho)),C("conjugate",C("absorbingJump",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I),C("operator",Rho))),Equal(C("norm",C("absorbingFailureOutput",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I,Rho)),C("norm",Out()))))),
                "The fixed absorbing successor is coordinate five of B(Fin6,H). The map absorbingJump is iota_f after the actual referenceJump. Expanding its adjoint conjugation gives iota_f times the reference output times pi_f. The positive compression of the same input is trace class on H; embedding it in coordinate f preserves its trace and positive trace norm. Scalar homogeneity therefore shows that absorbingFailureOutput is exactly the six-coordinate Kraus output and has the same trace norm as failureOutput. This conclusion starts from a five-coordinate live joint input. It does not assert the extension for a general initially live-and-stopped six-coordinate input or its terminal coherences."),
            Item("actual_output_mass_partition","All mode-block masses belong to the same joint input",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("rho",C("TraceClass",C("B",C("Fin",D(5)),F.Id("H"))))],
                    Imp(Le(D(0),C("operator",Rho)),Equal(C("sumReferenceBlockNorms",Rho),C("norm",Rho)))),
                "For a positive trace-class input the reference block at mode i is pi_i rho iota_i. Its positive trace norm is its real trace. Splitting the trace of rho on the full finite block Hilbert basis proves that the five trace norms sum to the trace norm of rho. For a normalized positive input their sum is one. The blocks are all taken from the same rho; off-diagonal reference correlations are not replaced by independently selected inputs."))));
    private static readonly Formula R=F.Id("Real"),Rho=F.Id("rho"),I=F.Id("i");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula Coeff()=>C("coefficient",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I);
    private static Formula J()=>C("referenceJump",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I);
    private static Formula Out()=>C("failureOutput",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),I,Rho);
    private static Formula Hyp()=>Conj(Conj(C("lessThanHalf",F.Id("c")),Conj(C("interior",F.Id("a"),F.Id("c")),C("interior",F.Id("k"),F.Id("c")))),Conj(Le(D(0),F.Id("S")),Le(D(0),C("apply",F.Id("g"),I))));
    private static DocumentBlock Item(string name,string title,Formula f,string text)=>Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceKraus."+name),H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Equal(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Conj(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string name,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..xs]);
}
