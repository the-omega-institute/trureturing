using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;
internal sealed class OriginalReferenceLegOutputDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Original affine-leg outputs in the trace-norm space of an arbitrary reference.",
        H("Tensor action and measurable quantum outputs"),Blocks(
            Item("tensor_jump_intertwining","The original row acts only on the live system",
                TensorStatement(),
                "The system is the five-dimensional Euclidean space and H is any complete complex Hilbert space. The finite tensor isometry sends u tensor x to the vector with coordinates u_i x. The amplified row is obtained from the literal original jumpKraus coefficients. On a simple tensor, distributing the finite row sum gives the original scalar row action on u multiplied by x. Tensor induction extends this identity to every joint vector. The algebraic tensor is already complete because its finite-system coordinate realization is a complete finite Hilbert sum. Thus the equation is the action tensored with the unchanged reference on the entire joint space, including entangled vectors."),
            Item("affine_failure_bochner","Actual affine-leg Bochner outputs on every Borel event",
                BochnerStatement(),
                "L has c<1/2, positive duration, and endpoints strictly between zero and c. Its height is the literal affine path, its hazard is the original positive-part logarithmic hazard, its survival is exp of minus its hazard integral, and its rate subtracts the actual logarithmic probability derivative. The coefficient is g_i(t) S(t) p_i(k(t))/p_i(x). It equals the supplied affine-leg density divided by the positive initial probability p_i(x). Measurability of derivatives, continuity of the hazard primitive on the valid interval, and measurability of the affine height give scalar strong measurability. The already established finite marked probability law bounds each positive mode-density integral, so the coefficient is integrable. For fixed rho and i the output lies in the one-dimensional span of the same reference compression pi_i rho iota_i, even when the reference and trace-class space are nonseparable. Scalar multiplication proves Bochner integrability in the genuine trace norm. On the intersection of every Borel event E with (0,L.duration] the integral is the scalar coefficient integral times that fixed compression. The pointwise Kraus identity identifies this density with the actual output; it does not prescribe an output law. No normalization, product-state or finite-rank restriction is imposed. This theorem concerns one actual affine leg. Repeated-prefix coefficient masses, the early/late trace-distance equality, the operational supremum, the general six-dimensional input extension and the inverse application require further conclusions."),
            Item("affine_failure_event","Positive actual outputs on every Borel event",
                EventStatement(),
                "For every original affine leg, every mode, every complete complex Hilbert reference, every positive trace-class joint input and every Borel time event E, the density is integrable on D=(0,L.duration] intersect E. At every time in D its underlying operator is the literal amplified Kraus conjugation of that same input. The coefficient is nonnegative on this interval, so the Bochner event integral is positive. Scalar factorization in TraceClass H proves the exact identity norm(integral_D F)=integral_D norm(F), using the genuine trace norm. No separability, product-state, finite-reference or input normalization condition is imposed."))));
    private static Formula TensorStatement()
    {
        Formula h=F.Id("H"), i=F.Id("i"), z=F.Id("z");
        Formula lhs=C("referenceJumpAfterCoordinates",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),i,z);
        Formula row=C("originalAbsorbingRow",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("S"),F.Id("g"),i);
        Formula rhs=C("scalarTensorIdentification",C("tensorMap",row,C("identity",h),z));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("c",R),V("a",R),V("k",R),V("S",R),V("g",C("Functions",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("z",C("Tensor",C("EuclideanSpace",C("Fin",D(5))),h))],Eq(lhs,rhs));
    }
    private static Formula BochnerStatement()
    {
        Formula h=F.Id("H"), l=F.Id("L"), i=F.Id("i"), rho=F.Id("rho"), e=F.Id("E");
        Formula output=C("actualFailureOutput",l,i,rho);
        Formula eventDomain=C("intersection",C("Ioc",D(0),C("duration",l)),e);
        Formula integral=Eq(C("integralOnEvent",output,eventDomain),C("smul",C("integralOnEvent",C("actualCoefficient",l,i),eventDomain),C("referenceCompression",rho,i)));
        Formula events=All([V("E",C("Set",R))],Imp(C("MeasurableSet",e),integral));
        Formula integrable=C("IntegrableOnTraceNorm",output,C("Ioc",D(0),C("duration",l)));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("L",F.Id("OriginalAffineLeg")),V("i",C("Fin",D(5))),V("rho",C("TraceClass",C("Blocks",C("Fin",D(5)),h)))],Imp(C("Positive",rho),And(integrable,events)));
    }
    private static Formula EventStatement()
    {
        Formula h=F.Id("H"), l=F.Id("L"), i=F.Id("i"), rho=F.Id("rho"), e=F.Id("E");
        Formula domain=C("intersection",C("Ioc",D(0),C("duration",l)),e);
        Formula output=C("actualFailureOutput",l,i,rho);
        Formula integral=C("integralOnEvent",output,domain);
        Formula body=And(C("IntegrableOnTraceNorm",output,domain),And(C("pointwiseActualKrausConjugation",output,l,i,rho,domain),And(C("Positive",integral),Eq(C("norm",integral),C("integralOnEvent",C("normFunction",output),domain)))));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("L",F.Id("OriginalAffineLeg")),V("i",C("Fin",D(5))),V("rho",C("TraceClass",C("Blocks",C("Fin",D(5)),h))),V("E",C("Set",R))],Imp(And(C("Positive",rho),C("MeasurableSet",e)),body));
    }
    private static readonly Formula R=F.Id("Real");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static DocumentBlock Item(string name,string title,Formula f,string text)=>Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceLegOutput."+name),H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string name,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..xs]);
}
