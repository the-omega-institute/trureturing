using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AsynchronousZeroDiagonalStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed three-block family has a sharp boundary between convergence for every bounded constant delay and explicit nondecaying real histories.",
        H("A sharp boundary for real asynchronous histories"),
        Blocks(
            Paragraph(Text("All coordinates and initial histories are real. History slot zero is the newest slot. "
                + "For the three singleton blocks, write B(c,d,δ,K)=asyncMatrix (family c d) δ K, using the constant-delay history matrix. "
                + "Its newest row is (By)₀,ᵢ=Σⱼ Mᵢⱼ yδⱼᵢ,ⱼ, with source-to-destination delay δⱼᵢ; its other rows satisfy (By)ₛ,ᵢ=yₛ₋₁,ᵢ. "
                + "Thus Bᵗy is the actual history after t updates, not a free trajectory. "
                + "In the formulas e₀=(0,⟨0,0⟩) is the newest coordinate in block zero, ev(v,e₀)=v(e₀), and mulVec(B,y) is Matrix.mulVec B y.")),
            Def("coord", "Coord", "Three singleton block coordinates",
                "Coord is Vtx (fun i : Fin 3 => 1): each coordinate is a block i in Fin 3 together with its unique internal coordinate in Fin 1."),
            Def("history", "History", "Every retained history slot",
                "For each natural K, History K is Fin (K+1) × Coord. An arbitrary function y : History K → R prescribes every real slot from time −K through time zero."),
            Def("family", "family", "The signed zero-diagonal family",
                "For arbitrary real c,d, family c d is the matrix on Coord with rows (0,1,1), (c,0,0), and (−d,0,0), read by block coordinate. All three diagonal entries vanish."),
            Def("fixed-delay", "fixedDelay", "A fixed positive remote-delay array",
                "The fixedDelay array, written fixedDelay in the formula and δ* in the explanation, has rows (0,1,2), (1,0,1), and (2,1,0). It has zero local delays, positive remote delays and maximum delay two."),
            Def("bounded", "bounded", "Nonnegative arrays bounded by K",
                "For K in N and δ : Fin 3 → Fin 3 → N, bounded K δ means δᵢᵢ=0 for every i and δᵢⱼ≤K for every i,j. Remote entries may be zero."),
            Def("remote-positive", "remotePositive", "Positive remote entries",
                "remotePositive K δ means bounded K δ together with 0<δᵢⱼ whenever i≠j. Entries on zero matrix coefficients still satisfy this requirement."),
            Def("stable", "stable", "Convergence for every real initial history",
                "stable c d K δ means that, for every y : History K → R, the newest-slot vector i ↦ (B(c,d,δ,K)ᵗ y)(0,i) tends to the zero vector as the natural time t tends to infinity. No bound, sign condition or compatibility condition is imposed on y."),
            Describe.Lean(DescribeId.Create("sharp-delay-boundary"),
                DeclarationHandle.Create(Prefix + "whole_theorem_three_one"),
                H("All bounded delays and explicit boundary histories"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put d=c−λ² and S=2c−λ². The formal theorem allows arbitrary real λ,c with λ²≤c, so c≥0 and d≥0, including zero endpoints. The source theorem under 0<λ<1 is a direct instance of this stronger statement. "
                    + "When S<1, positive coordinate weights make the absolute update rows strictly contractive. "
                    + "Weights on the older history slots then give a geometric bound for every coordinate of every matrix power applied to an arbitrary real history. "
                    + "The bound tends to zero and therefore also gives convergence of the newest-slot vector. Its rate may depend on K; no single rate independent of K is asserted. "
                    + "When S≥1, one can choose a positive r≥1 with r⁶=cr²+d, taking r=1 at S=1 and r>1 at S>1. "
                    + "For z=ir, the real parts of zᵗ, czᵗ⁻² and −dzᵗ⁻³ satisfy the three delayed update equations for every integer t. "
                    + "Their values at times −K through zero form a real history for δ*, and its matrix-power orbit is exactly this solution. "
                    + "At time 4m the newest first coordinate equals r⁴ᵐ. For r=1 the entire history orbit is four-periodic and cannot tend to zero; for r>1 this subsequence grows exponentially. "
                    + "The same fixed array is available in both bounded classes whenever K≥2. No fixed-bound necessity is asserted for K=0 or K=1."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Def(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => name switch
    {
        "λ" => LambdaLower,
        "δ" => DeltaLower,
        _ => F.Id(name),
    };
    private static Formula P(Formula a) => Seq(Open,a,Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(X(name))),[..args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall,Sp,P(Seq(X(name),Colon,Sp,type)),Comma,Sp,P(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists,Sp,P(Seq(X(name),Colon,Sp,type)),Comma,Sp,P(body));
    private static Formula R() => Seq(Mathbb,Grp(X("R")));
    private static Formula N() => Seq(Mathbb,Grp(X("N")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.And,P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Implies,P(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Iff,P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a,b);

    private static Formula Statement()
    {
        var lambda=X("λ"); var c=X("c"); var k=X("K"); var delta=X("δ");
        var d=Sub(c,Pow(lambda,D(2))); var s=Sub(Mul(D(2),c),Pow(lambda,D(2)));
        var deltaStar=X("fixedDelay");
        var delayType=Arr(Call("Fin",D(3)),Arr(Call("Fin",D(3)),N()));
        var below=LT(s,D(1));
        Formula Stable(Formula bound, Formula delays) => Call("stable",c,d,bound,delays);
        Formula Every(string predicate) => All("δ",delayType,
            Imp(Call(predicate,k,delta),Stable(k,delta)));
        var allBounds=IffF(below,All("K",N(),Every("bounded")));
        var fixedArray=IffF(below,Stable(D(2),deltaStar));
        var fixedBounds=All("K",N(),Imp(LE(D(2),k),
            And(IffF(below,Every("bounded")),IffF(below,Every("remotePositive")))));
        Formula Orbit(Formula time) => Call("mulVec",
            Pow(Call("B",c,d,deltaStar,k),time),X("y"));
        Formula First(Formula time) => Call("ev",Orbit(time),new Formula.Subscript(X("e"),D(0)));
        var historyType=Arr(Call("History",k),R());
        var periodic=Imp(Eq(s,D(1)),All("K",N(),Imp(LE(D(2),k),
            Ex("y",historyType,And(
                All("t",N(),Eq(Orbit(Add(X("t"),D(4))),Orbit(X("t")))),
                All("m",N(),Eq(First(Mul(D(4),X("m"))),D(1))))))));
        var growing=Imp(LT(D(1),s),All("K",N(),Imp(LE(D(2),k),
            Ex("r",R(),And(LT(D(1),X("r")),Ex("y",historyType,
                All("m",N(),Eq(First(Mul(D(4),X("m"))),Pow(X("r"),Mul(D(4),X("m")))))))))));
        var body=And(allBounds,And(fixedArray,And(fixedBounds,And(periodic,growing))));
        return All("λ",R(),All("c",R(),Imp(LE(Pow(lambda,D(2)),c),body)));
    }
}
