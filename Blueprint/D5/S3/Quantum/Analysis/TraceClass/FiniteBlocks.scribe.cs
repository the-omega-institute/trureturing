using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class FiniteBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Hilbert sums preserve the full reference in each coordinate.",
        H("Positive trace-class blocks"), Blocks(
            Item("compression_nonneg", "Positive diagonal reference blocks",
                Joint(Imp(Le(D(0),T),Le(D(0),Comp()))),
                "H is any complete complex Hilbert space, I is any finite type with decidable equality, and B(I,H) is PiLp 2 with one copy of H per coordinate. The coordinate pi_i is bounded evaluation and its adjoint iota_i inserts a vector in coordinate i. Compression is the actual operator pi_i T iota_i on H. Its quadratic form is the quadratic form of T evaluated on iota_i x, so positivity passes to the reference block."),
            Item("compression_traceClass", "Trace-class compression to a different Hilbert space",
                Joint(Imp(Conj(Tc(T),Le(D(0),T)),Tc(Comp()))),
                "Choose an arbitrary Hilbert basis b of H. The vectors iota_i(b_u), indexed by I times the entire index set of b, form a Hilbert basis of B(I,H): orthogonality is coordinatewise, and a vector orthogonal to every such vector has every coordinate zero. Reindexing this basis by its vector range permits the basis-independent trace-class criterion. The summable nonnegative diagonal of positive T restricts to each fixed coordinate. Since the absolute value of a positive operator equals itself, this restricted family proves that pi_i T iota_i is trace class. No countability, finite rank, finite reference dimension, or product-state hypothesis occurs."),
            Item("trace_compression_sum", "Finite splitting of the same joint trace",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("I",F.Id("FiniteDecidableType")),V("T",C("End",C("B",I,Hh)))],
                    Imp(Conj(Tc(T),Le(D(0),T)),Equal(C("diagonalTraceSum",T),C("trace",T)))),
                "The trace on the block basis is the unconditional sum of the diagonal reference coefficients. Splitting its finite coordinate index gives sum_i Tr(pi_i T iota_i)=Tr(T). Every summand is computed from the same T; correlations in T are neither replaced nor independently chosen."),
            Item("embedding_traceClass", "Trace-class embedding into a fixed coordinate",
                Reference(Imp(Conj(Tc(A),Le(D(0),A)),Tc(Emb()))),
                "Embedding is iota_i A pi_i. It is positive, and its diagonal on the block basis vanishes outside coordinate i. The remaining diagonal is exactly that of A. Its summability proves trace class in the full joint space."),
            Item("embedding_trace_norm", "The fixed coordinate preserves positive trace and trace norm",
                Reference(Imp(Conj(Tc(A),Le(D(0),A)),Conj(Equal(C("trace",Emb()),C("trace",A)),Equal(C("traceNorm",Emb()),C("traceNorm",A))))),
                "Summing the embedding diagonal gives the unchanged complex trace. For positive trace-class operators the trace norm is the real trace, so the genuine trace norm is unchanged as well. In an absorbing output coordinate this is the isometric retention of the reference state."),
            Item("tensorCoordinates_tmul", "The tensor coordinates preserve the unchanged reference",
                All([V("H",F.Id("CompleteComplexHilbertSpace")),V("I",F.Id("FiniteDecidableType")),V("u",C("EuclideanSpace",I)),V("x",Hh),V("i",I)],
                    Equal(C("coordinate",C("tensorCoordinates",C("tensor",F.Id("u"),F.Id("x"))),i),C("smul",C("coordinate",F.Id("u"),i),F.Id("x")))),
                "tensorCoordinates is a complex linear isometry equivalence from the Hilbert tensor product of the finite scalar system and H onto B(I,H). On a simple tensor u tensor x its i-th coordinate is u_i times x. The inner product is first checked on simple tensors and then on all tensors by the tensor induction principle. The underlying linear equivalence is onto; since the finite Hilbert sum is complete, this tensor product is already complete. Thus no restriction to simple tensors, finite-dimensional references, or separable references is imposed."))));
    private static readonly Formula Hh=F.Id("H"), I=F.Id("I"), T=F.Id("T"), A=F.Id("A"), i=F.Id("i");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula Comp()=>C("compression",T,i);
    private static Formula Emb()=>C("embedding",A,i);
    private static Formula Tc(Formula x)=>C("IsTraceClass",x);
    private static Formula Joint(Formula body)=>All([V("H",F.Id("CompleteComplexHilbertSpace")),V("I",F.Id("FiniteDecidableType")),V("T",C("End",C("B",I,Hh))),V("i",I)],body);
    private static Formula Reference(Formula body)=>All([V("H",F.Id("CompleteComplexHilbertSpace")),V("I",F.Id("FiniteDecidableType")),V("A",C("End",Hh)),V("i",I)],body);
    private static DocumentBlock Item(string name,string title,Formula f,string text)=>Describe.Lean(
        DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks."+name),
        H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Equal(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Conj(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string name,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..xs]);
}
