using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritPerturbationAttainmentDocument : IScribeDocumentDefinition
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
    private static Formula Lt(Formula x, Formula y) => Seq(x, F.Lt, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Smul(Formula c, Formula m) => Call("SMul.smul",c,m);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static Formula Star(Formula m) => Call("star", m);
    private static Formula Adj(Formula m) => Call("Matrix.conjTranspose", m);
    private static Formula OfReal(Formula r) => Call("Complex.ofReal", r);
    private static Formula CastN(Formula n) => Parenthesized(Seq(n, Colon, R));
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula n => Id("n");
    private static Formula v => Id("v");
    private static Formula P => Id("P");
    private static Formula AB => Prod(Id("A"), Id("B"));
    private static Formula J => Prod(Fin(Int(3)), Fin(n));
    private static Formula Mj => Matrix(J,J,C);
    private static Formula Pure => Call("rhoPure",n,v);
    private static Formula Projector => Call("rhoProjector",n,P);
    private static Formula ApptDefinition()
    {
        var u=Call("val",Id("U"));
        var f=All("M",Matrix(AB,AB,C),Seq(Call("APPT",Id("M")),Iff,Sp,
            All("U",Call("unitaryGroup",AB,C),PSInt(Call("KickedIsingNegativityRefutation.partialTranspose",Mul(Mul(u,Id("M")),Adj(u)))))));
        f=Seq(Bracket(Call("Fintype",Id("A"))),Sp,Bracket(Call("Fintype",Id("B"))),Sp,
            Bracket(Call("DecidableEq",Id("A"))),Sp,Bracket(Call("DecidableEq",Id("B"))),Sp,f);
        return All("A",Id("Type"),All("B",Id("Type"),f));
    }
    private static Formula PureDefinition() => All("n",N,All("v",Arrow(J,C),
        Eq(Pure,Smul(OfReal(Frac(Int(1),Add(Mul(Int(3),CastN(n)),Int(2)))),
            Parenthesized(Add(Int(1),Smul(Int(2),Call("Matrix.vecMulVec",v,Star(v)))))))));
    private static Formula ProjectorDefinition() => All("n",N,All("P",Mj,
        Eq(Projector,Smul(OfReal(Frac(Int(1),Mul(Int(4),CastN(n)))),Parenthesized(Add(Int(1),P))))));
    private static Formula PureStatement()
    {
        var ij=Id("ij");
        var norm=Eq(Sum("ij",J,Mul(Star(Call("v",ij)),Call("v",ij))),Int(1));
        var value=OfReal(Frac(Add(Mul(Int(3),CastN(n)),Int(8)),Pow(Add(Mul(Int(3),CastN(n)),Int(2)),2)));
        return All("n",N,All("v",Arrow(J,C),Imp(norm,
            And(Call("APPT",Pure),PSInt(Pure),Eq(Trace(Pure),Int(1)),Eq(Trace(Mul(Pure,Pure)),value)))));
    }
    private static Formula ProjectorStatement() => All("n",N,Imp(Lt(Int(0),n),All("P",Mj,
        Imp(And(Call("Matrix.IsHermitian",P),Eq(Mul(P,P),P),Eq(Call("Matrix.rank",P),n)),
            And(Call("APPT",Projector),PSInt(Projector),Eq(Trace(Projector),Int(1)),
                Eq(Trace(Mul(Projector,Projector)),OfReal(Frac(Int(3),Mul(Int(8),CastN(n))))))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit rank-one and projector perturbations attain the two candidate qutrit APPT purities.",
        H("Qutrit APPT attaining states"),Blocks(
            Desc("QutritPerturbationAttainment","APPT","Literal absolute PPT predicate",ApptDefinition(),
                "Ahiable–Kothakonda–Winter, page 2: Defined analogously to absolutely separable states, absolute PPT states are those states which remain PPT after global unitary rotations and have been completely characterized across all dimensions [17]. Here unitaryGroup is Mathlib's group of unitary matrices and val displays its matrix coercion. The predicate alone does not include density normalization. The partialTranspose operator is reused from KickedIsingNegativityRefutation and has entry formula M((i,l),(k,j)).",
                provenance:AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry"))),
            Desc("QutritPerturbationAttainment","rhoPure","Rank-one perturbation",PureDefinition(),
                "The scalar coefficient is Complex.ofReal of a real quotient. The numeral one is the identity Matrix. The vector is indexed by Fin 3 × Fin n and star acts pointwise."),
            Desc("QutritPerturbationAttainment","rhoProjector","Projector perturbation",ProjectorDefinition(),
                "The scalar is Complex.ofReal of the real quotient 1/(4n). This definition does not itself assume that P is an orthogonal projector."),
            Desc("QutritPerturbationAttainment","pure_attainment","Normalized-vector attainment",PureStatement(),
                "The normalization hypothesis is a complex equality. An explicit antisymmetric Gram complement makes the partial transpose positive under every global unitary; the normalized perturbation is positive, has trace one, and has the displayed complex trace-square.",DescribeRole.Theorem),
            Desc("QutritPerturbationAttainment","projector_attainment","Rank-n projector attainment",ProjectorStatement(),
                "For positive n, a Hermitian idempotent of rank n produces a density matrix of purity 3/(8n). The proof constructs a positive qutrit Kraus decomposition after conjugation and takes the full transpose to obtain the second-factor convention.",DescribeRole.Theorem))));
}
