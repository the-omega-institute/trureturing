using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class BooleanCollectiveLaddersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/BooleanCollectiveLadders.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite primitive raising strings span the full complex Boolean space and satisfy exact endpoint, weight, norm and orthogonality identities.",
        H("Complex Boolean primitive-string algebra"),
        Blocks(
            Paragraph(Text("The carrier is V(N) = EuclideanSpace(ℂ, Fin(N) → Fin(2)), with its complex Hermitian inner product. Every configuration is retained. A zero bit denotes membership. These are the single-block algebra and spanning prerequisites in TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION, Theorem 6.2, equations (6.6)–(6.8). The classical Boolean representation is cited there to Srinivasan, arXiv:1001.0280v2, and Feinsilver, arXiv:1102.0368v2; no claim of mathematical novelty is made.")),
            Node("occupancy", "Occupancy", Occupancy(), DescribeRole.Definition),
            Node("U", "The native collective raising map", Native(true), DescribeRole.Definition),
            Node("L", "The native collective lowering map", Native(false), DescribeRole.Definition),
            Node("number", "The number operator", Number(), DescribeRole.Definition),
            Node("Z", "Centered occupancy", Centered(), DescribeRole.Definition),
            Node("rankSpace", "Homogeneous rank space", Rank(), DescribeRole.Definition),
            Node("primitive", "Every primitive vector", Primitive(), DescribeRole.Definition),
            Node("finitePrimitiveStrings", "The finite strings", Strings(), DescribeRole.Definition),
            Node("result", "Span and exact primitive-string identities", Result(), DescribeRole.Theorem),
            Paragraph(Text("The raising and lowering maps are Matrix.toEuclideanLin of the existing PronkoFredkinAntiAdjointExpansion.totalPlus and totalMinus, using the existing sigmaPlus, sigmaMinus and site operators. Their tensor multiplication is reused from StabilizerPairLocalUnitaryInequivalence.tensor_mul. The proof derives the concrete commutator and complex adjoint relation. At each rank, orthogonal decomposition into the image of the preceding rank and its complement constructs primitive generators; induction proves full span. Thus neither a complete basis nor a homogeneous complement is an assumption. The pinned mathlib sl₂ primitive-vector theorems supply the recurrence and terminal zero on the whole nonzero carrier, including primitive strings of spin zero.")),
            Paragraph(Text("In the formulas, powers act by composition, ⟪v,w⟫ is complex Hermitian inner product, and scalars act on the left. Subtraction in the natural quantities d = 2S−2t and S−t is truncated; the lowering coefficient and weight are interpreted in ℂ after casting their natural operands. The notation scalar·vector denotes complex scalar multiplication. descFactorial(d,q) is the natural descending product ∏_{a=0}^{q−1}(d−a), equal to d!/(d−q)! when q≤d. The zero-power and zero-deficit cases are included. The result permits any primitive vector, without a reality restriction or a restriction to the permutation-invariant sector.")),
            Paragraph(Text("The multiplicity identity dim P(2S,t)=choose(2S,t)−previousChoose(2S,t), with previousChoose(2S,0)=0, is not proved here. Selection and normalization of a complete orthonormal family, a unitary onto the sum of native spin spaces, and its U/L/Z intertwiners remain open. Graph tensors, half-filling restrictions, projectors, adjacency, and the energy gap in Theorem 6.2 are also outside this result."))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("boolean-collective-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(name switch {
                "occupancy" => "Every zero bit contributes one occupied coordinate.",
                "U" => "This is the existing unweighted totalPlus matrix acting on Euclidean coordinates.",
                "L" => "This is the existing unweighted totalMinus matrix, the Hermitian adjoint of U.",
                "number" => "The number operator multiplies each configuration coefficient by its occupancy.",
                "Z" => "The identity shift centers occupancy at half of N, using complex scalar division.",
                "rankSpace" => "Homogeneous vectors have support only at the stated occupancy.",
                "primitive" => "A primitive vector is homogeneous and is annihilated by the actual lowering map.",
                "finitePrimitiveStrings" => "All primitive vacua are included, including the spin-zero sector t=S; q=0 is retained.",
                "result" => "The finite span, cutoff, endpoint, lowering coefficient, weight, norm and orthogonality clauses all hold jointly on the same full complex carrier.",
                _ => throw new InvalidOperationException("Unknown declaration.")
            }))), role);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula V(Formula n) => Call("V", n);
    private static Formula Config(Formula n) => new Formula.TypeArrow(Call("Fin", n), Call("Fin", D(2)));
    private static Formula All(string x, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Call(string f, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(f))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Pow(Formula n, Formula q, Formula v) => At(new Formula.Power(Call("U", n), q), v);
    private static Formula Inner(Formula v, Formula w) => Call("innerC", v, w);
    private static Formula Smul(Formula c, Formula v) => Seq(c, Sp, Cdot, Sp, v);
    private static Formula P(Formula n, Formula t) => Call("primitive", n, t);
    private static Formula Occupancy()
    {
        var n=F.Id("N"); var x=F.Id("x"); var i=F.Id("i");
        return All("N",N(),All("x",Config(n),Eq(Call("occupancy",x),
            Seq(new Formula.Subscript(F.Sum,Seq(i,Sp,InMacro,Sp,Call("Fin",n))),Sp,
                Call("ite",Eq(At(x,i),D(0)),D(1),D(0))))));
    }
    private static Formula Native(bool up)
    {
        var n=F.Id("N");
        return All("N",N(),Eq(Call(up?"U":"L",n),Call("toEuclideanLin",Call(up?"totalPlus":"totalMinus",n))));
    }
    private static Formula Number()
    {
        var n=F.Id("N");var v=F.Id("v");var x=F.Id("x");
        return All("N",N(),All("v",V(n),All("x",Config(n),
            Eq(At(At(Call("number",n),v),x),Mul(Call("occupancy",x),At(v,x))))));
    }
    private static Formula Centered()
    {
        var n=F.Id("N");
        return All("N",N(),Eq(Call("Z",n),Sub(Call("number",n),
            Smul(new Formula.Fraction(n,D(2)),Call("id",V(n))))));
    }
    private static Formula Rank()
    {
        var n=F.Id("N"); var t=F.Id("t"); var v=F.Id("v"); var x=F.Id("x");
        var support=All("x",Config(n),Imp(Ne(Call("occupancy",x),t),Eq(At(v,x),D(0))));
        var body=new Formula.Logic(Mem(v,Call("rankSpace",n,t)),FormulaLogicOperator.Iff,support);
        return All("N",N(),All("t",N(),All("v",V(n),body)));
    }
    private static Formula Primitive()
    {
        var n=F.Id("N"); var t=F.Id("t"); var v=F.Id("v");
        var body=new Formula.Logic(Mem(v,P(n,t)),FormulaLogicOperator.Iff,
            And(Mem(v,Call("rankSpace",n,t)),Eq(At(Call("L",n),v),D(0))));
        return All("N",N(),All("t",N(),All("v",V(n),body)));
    }
    private static Formula Strings()
    {
        var s=F.Id("S"); var n=Mul(D(2),s); var t=F.Id("t"); var q=F.Id("q"); var v=F.Id("v"); var w=F.Id("w");
        var power=Ex("q",N(),And(Le(q,Sub(n,Mul(D(2),t))),Eq(w,Pow(n,q,v))));
        var vacuum=Ex("v",V(n),And(Mem(v,P(n,t)),power));
        var body=new Formula.Logic(Mem(w,Call("finitePrimitiveStrings",s)),FormulaLogicOperator.Iff,
            Ex("t",N(),And(Le(t,s),vacuum)));
        return All("S",N(),All("w",V(n),body));
    }
    private static Formula Result()
    {
        var s=F.Id("S"); var n=Mul(D(2),s); var t=F.Id("t"); var tp=F.Id("tprime");
        var q=F.Id("q"); var r=F.Id("r"); var v=F.Id("v"); var w=F.Id("w"); var d=Sub(n,Mul(D(2),t));
        var span=Eq(Call("span",C(),Call("finitePrimitiveStrings",s)),Call("top",V(n)));
        var cutoff=All("t",N(),All("v",V(n),Imp(Mem(v,P(n,t)),Imp(Ne(v,D(0)),Le(t,s)))));
        var norm=Imp(Le(q,d),Eq(Inner(Pow(n,q,v),Pow(n,q,v)),
            Mul(Mul(Call("factorial",q),Call("descFactorial",d,q)),Inner(v,v))));
        var recur=Eq(At(Call("L",n),Pow(n,Add(q,D(1)),v)),
            Smul(Mul(Add(q,D(1)),Sub(Sub(n,Mul(D(2),t)),q)),Pow(n,q,v)));
        var weight=Eq(At(Call("Z",n),Pow(n,q,v)),Smul(Sub(q,Sub(s,t)),Pow(n,q,v)));
        var identities=And(Eq(Pow(n,Add(d,D(1)),v),D(0)),All("q",N(),And(recur,And(weight,norm))));
        var algebra=All("t",N(),Imp(Le(t,s),All("v",V(n),Imp(Mem(v,P(n,t)),identities))));
        var stringOrth=Imp(Eq(Inner(v,w),D(0)),All("q",N(),All("r",N(),
            Eq(Inner(Pow(n,q,v),Pow(n,r,w)),D(0)))));
        var rankOrth=Imp(Ne(t,tp),Eq(Inner(v,w),D(0)));
        var orth=All("t",N(),All("tprime",N(),All("v",V(n),All("w",V(n),
            Imp(Mem(v,P(n,t)),Imp(Mem(w,P(n,tp)),And(rankOrth,stringOrth)))))));
        return All("S",N(),Imp(Le(D(1),s),And(span,And(cutoff,And(algebra,orth)))));
    }
}
