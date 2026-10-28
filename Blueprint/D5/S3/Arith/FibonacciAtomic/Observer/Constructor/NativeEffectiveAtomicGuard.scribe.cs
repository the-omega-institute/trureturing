using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeEffectiveAtomicGuardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "NativeEffectiveAtomicGuard",H("Effective atomic observations of guarded completed systems"),Blocks(
            Describe.Lean(DescribeId.Create("native-effective-constant-semantics"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.constant_holds"),
                H("Boolean constants in finite Presburger syntax"),ConstantStatement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("The constant constructor produces the quantifier-free truth or falsity formula according to its Boolean argument. Its semantics is used by the atomic and image formula constructors, including empty conjunctions and disjunctions."))
                ),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-effective-atomic-guard"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.atomic_guard_correct"),
                H("A total finite formula for each exact atomic observation"),AtomicStatement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("An input I retains its original natural parameter tuple p, integer affine indices, Presburger guard, optional state definitions and repeated expression occurrences. Legal inputs satisfy the original guard and the nonnegativity of every affine index. The terminal-rank map is exactly toNat of those same affine expressions, so every repeated terminal shares its original rank.")),
                    Paragraph(Text("The definitions are pair-guarded: a state-dependent defining right side has a pair root. A mode fixes an undefined state to its specified small atom or assigns the leafless Omega. The canonical completed tuple is the unique extension of that free assignment. All finite and infinite completed values are permitted, including non-rational outputs.")),
                    Paragraph(Text("For a fixed natural target rank j, atomicGuard constructs finite Presburger syntax expressing equality of an arbitrary expression value with the actual atomic iterate T(j). A ground is compared with the finite native tree for T(j). A parameter token at offset c uses two affine inequalities expressing q(p)+c=j. Omega gives falsity. A decorated state rho(a)Y has an atomic value T(j) exactly when a is at most j and Y has value T(j-a); subtraction occurs only under that explicit inequality.")),
                    Paragraph(Text("A pair can equal T(j) only for j at least two, when its ordered children must equal T(j-1) and T(j-2). State formulas unfold a defining right side. Every recursive state query below such a pair has strictly smaller target rank. A well-founded recursive definition therefore constructs total finite syntax without selecting a semantic normal form. Its correctness follows by induction on the target rank and on finite expression syntax, using the exact native atomic predecessor and pair-parse laws.")),
                    Paragraph(Text("The displayed equivalence concerns an exact finite terminal observation of a whole completed value. It is the terminal test used in the image-language construction of Proposition 4.3. It imposes neither a finite-depth restriction nor a rationality restriction on the canonical value. The theorem alone does not assert simultaneous image-filter acceptance."))
                ),DescribeRole.Theorem)
        )));
    private static StatementSource ConstantStatement()=>StatementSource.FromAuthor(Disp(
        All("b",V("Bool"),All("x",Call("List",V("Int")),
            IffOf(Call("holds",Call("constant",V("b")),V("x")),EqOf(V("b"),V("true")))))));
    private static StatementSource AtomicStatement()
    {
        var n=V("n");var k=V("k");var m=V("m");var s=V("s");var input=V("I");var mode=V("mode");var p=V("p");var e=V("E");var j=V("j");
        var canonical=Call("canonical",Call("equations",input),Call("ranks",input,p),V("guarded"),mode);
        var body=IffOf(Call("holds",Call("atomicGuard",input,mode,e,j),Call("environment",p)),
            EqOf(Call("evaluate",Call("ranks",input,p),canonical,e),Call("atomic",j)));
        var statement=All("j",V("Nat"),body);
        statement=All("E",Call("Expression",k,m),statement);
        statement=Imp(Call("Legal",input,p),statement);
        statement=All("p",Arr(Call("Fin",n),V("Nat")),statement);
        statement=All("mode",Call("Mode",s,m),statement);
        statement=All("guarded",Call("Guarded",Call("equations",input)),statement);
        statement=All("I",Call("Input",n,k,m),statement);
        statement=All("s",V("Nat"),statement);
        statement=All("m",V("Nat"),statement);
        statement=All("k",V("Nat"),statement);
        statement=All("n",V("Nat"),statement);
        return StatementSource.FromAuthor(Disp(statement));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
