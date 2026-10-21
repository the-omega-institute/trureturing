using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class GenericAPPTDocument : IScribeDocumentDefinition
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
    private static Formula Star(Formula f) => new Formula.Power(Parenthesized(f), Id("H"));
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula Typed(Formula f, Formula type) => Parenthesized(Seq(f,Colon,type));
    private static Formula Binders(Formula body, params (string Name, Formula Type)[] binders)
    {
        foreach (var (name,type) in binders.Reverse()) body=name == "" ? Seq(OpenBracket,type,CloseBracket,Sp,body) : All(name,type,body);
        return body;
    }
    private static Formula Conjugate(Formula m, Formula v) => Mul(Mul(v,m),Star(v));
    private static Formula Diagonal(Formula f) => Call("Matrix.diagonal",f);
    private static Formula MapReal(Formula m) => Call("Matrix.map",Qualified("Complex","ofReal"),m);
    private static Formula FiniteBinders(Formula body, params string[] names)
    {
        foreach (var name in names.Reverse())
            body=Binders(body,(name,Id("Type")),("",Call("Fintype",Id(name))),("",Call("DecidableEq",Id(name))));
        return body;
    }
    private static Formula AB => Prod(Id("A"), Id("B"));
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula Adj(Formula m) => Call("Matrix.conjTranspose", m);
    private static Formula PartialTransposeDefinition()
    {
        var a=Id("A"); var b=Id("B"); var p=Id("p"); var q=Id("q"); var rho=Id("rho");
        var pair=Prod(a,b);
        Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x,Comma,y));
        return Disp(All("A",Id("Type"),All("B",Id("Type"),All("rho",Matrix(pair,pair,C),All("p",pair,All("q",pair,
            Eq(At(Call("partialTranspose",rho),p,q),At(rho,Pair(Call("fst",p),Call("snd",q)),Pair(Call("fst",q),Call("snd",p))))))))));
    }
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ApptDefinition()
    {
        var u=Call("val",Id("U"));
        var f=All("M",Matrix(AB,AB,C),Seq(Call("APPT",Id("M")),Iff,Sp,
            All("U",Call("unitaryGroup",AB,C),PSInt(Call("KickedIsingNegativityRefutation.partialTranspose",Mul(Mul(u,Id("M")),Adj(u)))))));
        f=Seq(Bracket(Call("Fintype",Id("A"))),Sp,Bracket(Call("Fintype",Id("B"))),Sp,
            Bracket(Call("DecidableEq",Id("A"))),Sp,Bracket(Call("DecidableEq",Id("B"))),Sp,f);
        return All("A",Id("Type"),All("B",Id("Type"),f));
    }

    private static Formula PermutationUnitaryDefinition()
    {
        var i=Id("I"); var e=Id("e");
        var matrix=Matrix(i,i,C);
        return Binders(Eq(Typed(Call("permutationU",e),matrix),Call("Equiv.permMatrix",e,C)),
            ("I",Id("Type")),("",Call("Fintype",i)),("",Call("DecidableEq",i)),
            ("e",Call("Equiv.Perm",i)));
    }

    private static Formula ExtendedUnitary(bool diagonal)
    {
        var i=Id("I"); var j=Id("J"); var t=Id("C"); var e=Id("e"); var v=Id("V");
        var sum=Parenthesized(Seq(j,Plus,t));
        var equivalence=Call("Equiv",sum,i);
        var unitary=Call("unitaryGroup",j,C);
        var u=Typed(Call("extendUnitaryAlong",e,v),Matrix(i,i,C));
        var inverse=Call("Equiv.symm",e);
        Formula body;
        if (!diagonal)
            body=Eq(u,Call("Matrix.submatrix",Call("Matrix.fromBlocks",Typed(v,Matrix(j,j,C)),Int(0),Int(0),Typed(Int(1),Matrix(t,t,C))),inverse,inverse));
        else
        {
            var x=Id("x"); var y=Id("y"); var index=Id("i");
            var packed=Parenthesized(Seq(Id("fun"),Sp,index,Sp,Mapsto,Sp,Call("Sum.elim",x,y,At(inverse,index))));
            body=Eq(Conjugate(Diagonal(packed),u),Call("Matrix.submatrix",
                Call("Matrix.fromBlocks",Conjugate(Diagonal(x),Typed(v,Matrix(j,j,C))),Int(0),Int(0),Diagonal(y)),inverse,inverse));
            body=Binders(body,("x",Arrow(j,C)),("y",Arrow(t,C)));
        }
        return FiniteBinders(Binders(body,("e",equivalence),("V",unitary)),"I","J","C");
    }

    private static Formula SharedStatement(string name)
    {
        var i=Id("I"); var m=Id("M"); var v=Id("V"); var e=Id("e");
        var coefficient=new Formula.Power(Typed(Call("Real.sqrt",Int(2)),C),Int(-1));
        var conjugate=Conjugate(m,Typed(v,Matrix(i,i,C)));
        if (name=="extendUnitaryAlong")
        {
            return ExtendedUnitary(false);
        }
        if (name=="extendUnitaryAlong_diagonal")
        {
            return ExtendedUnitary(true);
        }
        if (name=="c_square")
        {
            return Eq(Mul(coefficient,coefficient),Divide(Int(1),Int(2)));
        }
        if (name=="c_star")
        {
            return Eq(Call("star",coefficient),coefficient);
        }
        if (name=="real_psd_of_complex")
        {
            return FiniteBinders(All("M",Matrix(i,i,R),Imp(PSInt(MapReal(m)),PSInt(m))),"I");
        }
        if (name=="permutation_conjugate")
        {
            return FiniteBinders(Binders(Eq(Conjugate(m,Typed(Call("permutationU",e),Matrix(i,i,C))),
                Call("Matrix.submatrix",m,e,e)),("e",Call("Equiv.Perm",i)),("M",Matrix(i,i,C))),"I");
        }
        if (name=="appt_conjugate")
        {
            var product=Prod(Id("A"),Id("B"));
                var pconj=Conjugate(m,Typed(v,Matrix(product,product,C)));
                var before=Call("APPT",m); var after=Call("APPT",pconj);
                return FiniteBinders(Binders(Imp(before,after),
                    ("M",Matrix(product,product,C)),("V",Call("unitaryGroup",product,C))),"A","B");
        }
        throw new System.ArgumentOutOfRangeException(nameof(name));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared partial transpose, absolute PPT and unitary transport in arbitrary finite dimensions.",
        H("Generic APPT and unitary transport"), Blocks(
            Paragraph(Text("The definitions and consumed algebraic helpers retain their original full Lean names. The shared source owns their declarations; the dynamics, qutrit and four-by-five results import it. All finite types and matrices remain in the original domains, including empty types wherever permitted. No new theorem, wrapper or assumption is introduced. The coefficient identities normalize arbitrary-dimension Bell blocks. This source relocation supplies no new escape witness, certified instance, kernel verdict or utility acceptance. The unfinished audit contexts remain issues #16011 and #17689.")),
            Describe.Lean(DescribeId.Create("pathak-partialtranspose"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.partialTranspose"),
                H("Partial transposition"), StatementSource.FromAuthor(PartialTransposeDefinition()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/pathak2026mixedstate")),
                Blocks(Paragraph(Text("Equation (5), p. 2, uses partial transposition with respect to B. It swaps the two B indices while preserving the A indices. This definition allows different subsystem dimensions; the existing partialTransposeB is used directly for the equal two-qubit matrix in the proof."))), DescribeRole.Definition),
            Desc("QutritPerturbationAttainment","APPT","Literal absolute PPT predicate",ApptDefinition(),
                "Ahiable–Kothakonda–Winter, page 2: Defined analogously to absolutely separable states, absolute PPT states are those states which remain PPT after global unitary rotations and have been completely characterized across all dimensions [17]. Here unitaryGroup is Mathlib's group of unitary matrices and val displays its matrix coercion. The predicate alone does not include density normalization. The partialTranspose operator is reused from KickedIsingNegativityRefutation and has entry formula M((i,l),(k,j)).",
                provenance:AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry"))),
            Desc("QutritSpectralReduction","permutationU","Permutation unitary",PermutationUnitaryDefinition(),
                "The unitary associated with a permutation has its permutation matrix as its underlying complex matrix. It reorders the diagonal coordinates in spectral decompositions."),
            Desc("QutritSpectralReduction","extendUnitaryAlong","Extension by an identity block",SharedStatement("extendUnitaryAlong"),
                "Given an equivalence from a finite disjoint union to the ambient coordinates, extend a unitary on the first summand by the identity on the complement, then transport its matrix along the inverse equivalence. The old qutrit extension and the four-by-four local corner use this same construction."),
            Desc("QutritSpectralReduction","extendUnitaryAlong_diagonal","Conjugation of an extended diagonal",SharedStatement("extendUnitaryAlong_diagonal"),
                "Conjugating a packed diagonal by the extended unitary conjugates its first block and leaves its complementary diagonal block fixed. This identity transports matrices; it does not assert that a general coordinate equivalence commutes with partial transpose.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","c_square","The Bell coefficient square",SharedStatement("c_square"),
                "The reciprocal square root of two has square one half over the complex numbers. This is the existing scalar calculation used by the Bell principal-compression computation.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","c_star","The Bell coefficient is real",SharedStatement("c_star"),
                "Complex conjugation fixes the real Bell coefficient. The Bell principal-compression computation uses this identity.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","appt_conjugate","APPT survives global unitary conjugation",SharedStatement("appt_conjugate"),
                "For finite local index types, absolute positivity under partial transpose is preserved by global unitary conjugation. This follows by composing the tested unitaries, rather than transporting partial transpose through an arbitrary coordinate map.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","real_psd_of_complex","Real positivity descends from the complex cast",SharedStatement("real_psd_of_complex"),
                "A positive semidefinite complex cast of a finite real matrix forces the real matrix to be positive semidefinite. The proof restricts the complex quadratic form to real vectors and recovers real symmetry.",DescribeRole.Theorem),
            Desc("QutritSpectralReduction","permutation_conjugate","Permutation conjugation is coordinate reindexing",SharedStatement("permutation_conjugate"),
                "Conjugation by the permutation unitary gives the simultaneous row-and-column submatrix reindexing. The spectral packing argument uses this identity before testing APPT.",DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("appt-product-partial-transpose"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.product_partialTranspose"),
                H("Partial transpose on a product submatrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary types A, B, C and D, maps a:C to A and b:D to B, and a complex matrix M on A times B, taking the product submatrix along Prod.map a b commutes with partial transpose. No finiteness, injectivity, invertibility or positivity is required. The identity holds entry by entry."))), DescribeRole.Theorem))));
}
