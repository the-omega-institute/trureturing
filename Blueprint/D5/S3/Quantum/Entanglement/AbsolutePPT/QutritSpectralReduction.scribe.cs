using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritSpectralReductionDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Lt(Formula x, Formula y) => Seq(x, F.Lt, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula k => Id("k");
    private static Formula l => Id("l");
    private static Formula q => Id("q");
    private static Formula rho => Id("rho");
    private static Formula Dimension => Mul(Int(3),Parenthesized(Add(Int(3),k)));
    private static Formula J => Prod(Fin(Int(3)),Fin(Add(Int(3),k)));
    private static Formula Value(int i) => Call("l",Int(i));
    private static Formula KDefinition(string name, int diagonalMiddle, int upperRight)
    {
        Formula[] entries=[Mul(Int(2),Value(8)),Sub(Value(7),Value(0)),Sub(Value(upperRight),Value(1)),
            Sub(Value(7),Value(0)),Mul(Int(2),Value(diagonalMiddle)),Sub(Value(4),Value(2)),
            Sub(Value(upperRight),Value(1)),Sub(Value(4),Value(2)),Mul(Int(2),Value(3))];
        var matrix=Seq(Bang,Bang,OpenBracket,entries[0],Comma,entries[1],Comma,entries[2],Semi,entries[3],Comma,entries[4],Comma,entries[5],Semi,entries[6],Comma,entries[7],Comma,entries[8],CloseBracket);
        return All("l",Arrow(Fin(Int(9)),R),Eq(Call(name,l),matrix));
    }
    private static Formula BoundaryDefinition()
    {
        var v=Call("val",q);
        var index=Seq(Id("if"),Sp,Lt(v,Int(3)),Sp,Id("then"),Sp,v,Sp,Id("else"),Sp,Add(Mul(Int(3),k),v));
        var finIndex=Parenthesized(Seq(index,Colon,Fin(Dimension)));
        return All("k",N,All("l",Arrow(Fin(Dimension),R),All("q",Fin(Int(9)),
            Eq(Call("boundaryValues",k,l,q),Call("l",finIndex)))));
    }
    private static Formula SpectralStatement()
    {
        var boundary=Call("boundaryValues",k,l);
        var purity=Eq(Call("Complex.re",Trace(Mul(rho,rho))),Sum("i",Fin(Dimension),Pow(Call("l",Id("i")),2)));
        var spectral=And(Call("Antitone",l),All("i",Fin(Dimension),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(Dimension),Call("l",Id("i"))),Int(1)),PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)),purity);
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(Dimension),R))),Comma,Sp,spectral);
        return All("k",N,All("rho",Matrix(J,J,C),Imp(And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho)),exists)));
    }
    private static Formula Q => Seq(Mathbb, Grp(Id("Q")));
    private static Formula Z => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Star(Formula f) => new Formula.Power(Parenthesized(f), Id("H"));
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula Typed(Formula f, Formula type) => Parenthesized(Seq(f,Colon,type));
    private static Formula Binders(Formula body, params (string Name, Formula Type)[] binders)
    {
        foreach (var (name,type) in binders.Reverse()) body=name == "" ? Seq(OpenBracket,type,CloseBracket,Sp,body) : All(name,type,body);
        return body;
    }
    private static Formula CastDefinition(bool integer)
    {
        var i=Id("I"); var j=Id("J"); var a=Id("A");
        var name=integer ? "castIntMat" : "castMat";
        var cast=integer ? "Int.cast" : "Rat.cast";
        return Binders(Eq(Call(name,a,Id("i"),Id("j")),Typed(Call(cast,Call("A",Id("i"),Id("j"))),R)),
            ("I",Id("Type")),("J",Id("Type")),("A",Matrix(i,j,integer ? Z : Q)),("i",i),("j",j));
    }
    private static Formula CastArithmetic(bool integer, string operation)
    {
        var i=Id("I"); var j=Id("J"); var t=Id("K"); var a=Id("A"); var b=Id("B"); var d=Id("d");
        var field=integer ? Z : Q; var name=integer ? "castIntMat" : "castMat"; var cast=integer ? "Int.cast" : "Rat.cast";
        if (operation=="mul")
            return Binders(Eq(Call(name,Mul(a,b)),Mul(Call(name,a),Call(name,b))),
                ("I",Id("Type")),("J",Id("Type")),("K",Id("Type")),("",Call("Fintype",j)),
                ("A",Matrix(i,j,field)),("B",Matrix(j,t,field)));
        if (operation=="transpose")
            return Binders(Eq(Call(name,Call("Matrix.transpose",a)),Star(Call(name,a))),
                ("I",Id("Type")),("J",Id("Type")),("A",Matrix(i,j,field)));
        var castD=Seq(Id("fun"),Sp,Typed(Id("i"),i),Sp,Mapsto,Sp,Typed(Call(cast,Call("d",Id("i"))),R));
        return Binders(Eq(Call(name,Call("Matrix.diagonal",d)),Call("Matrix.diagonal",Parenthesized(castD))),
            ("I",Id("Type")),("",Call("DecidableEq",i)),("d",Arrow(i,field)));
    }
    private static Formula LDLStatement(bool integer)
    {
        var i=Id("I"); var j=Id("J"); var a=Id("A"); var ai=Id("AI"); var lower=Id("L"); var d=Id("d"); var scale=Id("s");
        var factor=Mul(Mul(lower,Call("Matrix.diagonal",d)),Call("Matrix.transpose",lower));
        var factorEq=Eq(integer ? ai : a,factor);
        var nonnegative=All("j",j,Le(Int(0),Call("d",Id("j"))));
        Formula body;
        if (integer)
        {
            var scaling=All("i",i,All("j",i,Eq(Call("A",Id("i"),Id("j")),
                Divide(Typed(Call("Int.cast",Call("AI",Id("i"),Id("j"))),Q),Typed(Call("Int.cast",scale),Q)))));
            body=Imp(And(scaling,factorEq,nonnegative,Lt(Int(0),scale)),PSInt(Call("castMat",a)));
            body=Binders(body,("A",Matrix(i,i,Q)),("AI",Matrix(i,i,Z)),("L",Matrix(i,j,Z)),("d",Arrow(j,Z)),("s",Z));
        }
        else body=Binders(Imp(And(factorEq,nonnegative),PSInt(Call("castMat",a))),
            ("A",Matrix(i,i,Q)),("L",Matrix(i,j,Q)),("d",Arrow(j,Q)));
        return Binders(body,("I",Id("Type")),("J",Id("Type")),("",Call("Fintype",j)),
            ("",Call("DecidableEq",j)),("",Call("Fintype",i)),("",Call("DecidableEq",i)));
    }
    private static Formula VectorCast(bool empty)
    {
        var n=Id("n"); var v=Id("v"); var x=Id("x"); var index=Id("i");
        var dimension=empty ? Int(0) : Add(n,Int(1));
        var vector=empty ? Typed(Qualified("Matrix","vecEmpty"),Arrow(Fin(Int(0)),Q)) : Call("Matrix.vecCons",x,v);
        var lhs=Seq(Id("fun"),Sp,Typed(index,Fin(dimension)),Sp,Mapsto,Sp,
            Typed(Call("Rat.cast",At(vector,index)),R));
        var tail=Seq(Id("fun"),Sp,Typed(index,Fin(n)),Sp,Mapsto,Sp,Typed(Call("Rat.cast",Call("v",index)),R));
        var rhs=empty ? Typed(Qualified("Matrix","vecEmpty"),Arrow(Fin(Int(0)),R)) :
            Call("Matrix.vecCons",Typed(Call("Rat.cast",x),R),Parenthesized(tail));
        var statement=Eq(Parenthesized(lhs),rhs);
        return empty ? statement : Binders(statement,("n",N),("x",Q),("v",Arrow(Fin(n),Q)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal qutrit APPT states yield ordered nonnegative spectral certificate coordinates constrained by both boundary LMIs.",
        H("Qutrit spectral reduction"),Blocks(
            Desc("QutritSpectralReduction","castMat","Rational matrix cast",CastDefinition(false),
                "The entrywise rational-to-real map preserves the row and column types."),
            Desc("QutritSpectralReduction","castIntMat","Integer matrix cast",CastDefinition(true),
                "The entrywise integer-to-real map preserves the row and column types."),
            Desc("QutritSpectralReduction","castMat_mul","Rational casts preserve matrix products",CastArithmetic(false,"mul"),
                "A finite inner index permits entrywise casting of the finite product sum.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","castMat_transpose","Rational transpose cast",CastArithmetic(false,"transpose"),
                "Real conjugation is trivial, so the cast transpose is the conjugate transpose.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","castMat_diagonal","Rational diagonal cast",CastArithmetic(false,"diagonal"),
                "Casting preserves each diagonal entry and the zero off-diagonal entries.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","castIntMat_mul","Integer casts preserve matrix products",CastArithmetic(true,"mul"),
                "A finite inner index permits entrywise casting of the finite product sum.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","castIntMat_transpose","Integer transpose cast",CastArithmetic(true,"transpose"),
                "Real conjugation is trivial, so the cast transpose is the conjugate transpose.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","castIntMat_diagonal","Integer diagonal cast",CastArithmetic(true,"diagonal"),
                "Casting preserves each diagonal entry and the zero off-diagonal entries.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","psd_of_rat_ldl","Positive rational LDL factorization",LDLStatement(false),
                "Nonnegative rational diagonal entries give a positive semidefinite real diagonal matrix. Conjugation by the cast rectangular factor preserves positivity. The finite-sector bounds apply this criterion to their rational matrices.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","psd_of_int_scaled_ldl","Positive scaled integer LDL factorization",LDLStatement(true),
                "An integer LDL factorization with nonnegative diagonal entries is positive semidefinite after casting. Division by a positive integer scale preserves positivity. The finite-sector bounds apply this criterion to their scaled integer Gram matrices.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","cast_vec_cons","Cast of a vector constructor",VectorCast(false),
                "Casting a rational vector with an initial coordinate gives the real vector constructor with both pieces cast.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","cast_vec_empty","Cast of the empty vector",VectorCast(true),
                "The cast empty rational vector equals the empty real vector.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","K1","First qutrit boundary matrix",KDefinition("K1",6,5),
                "The argument l has nine boundary values, in descending spectral order: the largest three and the smallest six. Indices are zero-based. This is the first real symmetric qutrit LMI in Hildebrand's spectral criterion (Equation (5), pages 5–6).",provenance:AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra"))),
            Desc("QutritSpectralReduction","K2","Second qutrit boundary matrix",KDefinition("K2",5,6),
                "The second qutrit LMI interchanges boundary indices 5 and 6 relative to K1. All matrix entries are real.",provenance:AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra"))),
            Desc("QutritSpectralReduction","boundaryValues","Boundary spectral coordinates",BoundaryDefinition(),
                "The dependent Fin constructor carries the displayed natural-number index and its bound proof. The first three coordinates are unchanged; the remaining six have index 3k+q. Here n=3+k, and the full dimension is 3(3+k)."),
            Desc("QutritSpectralReduction","spectral_reduction","Density-to-spectral-certificate reduction",SpectralStatement(),
                "For every k and every positive semidefinite trace-one Matrix on Fin 3 × Fin (3+k), literal APPT yields antitone nonnegative real certificate coordinates with mass one, both positive boundary matrices, and the same real trace-square. The public conclusion does not identify these coordinates with rho's eigenvalues; the proof chooses sorted eigenvalues. The proof constructs Bell and permutation unitaries, compresses their partial transposes, and sorts the eigenvalues. This is the necessary direction of Hildebrand, Corollary 4, pages 5–6, together with the standard trace identities.",DescribeRole.Theorem,AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra"))))));
}
