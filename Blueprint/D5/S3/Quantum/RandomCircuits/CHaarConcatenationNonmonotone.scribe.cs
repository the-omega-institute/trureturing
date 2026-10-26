using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.RandomCircuits;

internal sealed class CHaarConcatenationNonmonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/QuantumChannels/duschenesgarciamartinholmescerezo2026moments");
    private const string ChannelQuote = "Page 5: \"Thus the action of any quantum channel is\" followed by Lambda(X) = Tr_E[U_Lambda(X tensor nu_E)U_Lambda dagger]. Appendix B, Definition 4, page 25: \"Using the Stinespring formalism, we can re-write this average as a twirl with respect to the Haar ensemble of unitaries acting on t copies of a composite space, of a system and environment H ⊗ E of dimensions d,d_E, and a local pure environment state ν_E ∈ B[E],\" The system and environment are Fin d and Fin e; Matrix.single 0 0 1 is the fixed pure environment state. The existing partialTraceRight is precisely the sum over the environment coordinate.";
    private const string MomentQuote = "Page 3: \"We can then define the t-th order moment operator as the superoperator of the t-th order twirl,\" followed by equation (9). The entry at r,c integrates the product of the t channel matrix-unit entries with the same Haar unitary U. This defines every order t, not only the second order.";
    private const string ClaimQuote = "Appendix B, Conjecture 1, page 32: \"it is conjectured that such a hierarchy holds for all concatenations k, orders t, and dimensions d,d_E. Further, it is conjectured that the cHaar norm is monotonically non-increasing with environment dimension and concatenations,\" followed by the displayed concatenation inequality for every k′ ≥ k. Here d,d_E are d,e; the order is t; k and j are positive concatenation counts with k ≤ j. Page 3: \"The choice of norm ∥·∥ is task-dependent, and unless noted, we use the Hilbert-Schmidt norm as it is overall the simplest to compute.\" The squared Hilbert-Schmidt norm of the Liouville matrix is the existing RHLinalg.frobSq, equal to the double sum of Complex.normSq. The environment-dimension clause is a separate assertion.";

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("chaar-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second cHaar moment at system and environment dimension two has larger squared Hilbert-Schmidt norm after five concatenations than after four.",
        H("Concatenation can increase the cHaar moment norm"),
        Blocks(
            Node("channel", "The cHaar channel", Channel(), ChannelQuote,
                "cHaarChannel", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("moment", "The literal moment operator", Moment(), MomentQuote,
                "momentOp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("norm", "The squared Hilbert-Schmidt norm", Norm(),
                "The squared Hilbert-Schmidt norm is the sum of Complex.normSq over all matrix entries. The concatenation assertion compares this quantity for two powers of the moment operator.",
                "hsNormSq", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The concatenation monotonicity assertion", Claim(), ClaimQuote,
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("swap-hermitian", "The coordinate swap is Hermitian", SwapHermitian(),
                "The permutation matrix of the coordinate swap equals its conjugate transpose.",
                "swapHermitian", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("swap-square", "The coordinate swap is an involution", SwapSquare(),
                "Applying the coordinate swap twice gives the identity matrix.",
                "swapSquare", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The concatenation assertion is false", new Formula.Not(Call("claim")),
                "At d = e = t = 2 the fourth power has squared norm 1213852/1171875, and the fifth has squared norm 30362908/29296875. Their difference is 5536/9765625, which is positive. In the rational identity/swap basis, the decaying eigenmode coexists with a growing coefficient towards a non-orthogonal limiting projection.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(
                    "duschenes-garciamartin-holmes-cerezo-2026-chaar-concatenation"), ResolutionKind.Refuted))
        ), []));

    private static Formula Channel()
    {
        Formula d=F.Id("d"), e=F.Id("e"), u=F.Id("U"), x=F.Id("X");
        Formula ancilla=Cast(QCall("Matrix.single",D(0),D(0),D(1)), MatrixOf(Fin(e)));
        Formula kronecker=QCall("Matrix.kroneckerMap", Lambda("a",Lambda("b",Mul(F.Id("a"),F.Id("b")))),x,ancilla);
        Formula body=QCall("D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight",
            Mul(Mul(u,kronecker),Call("star",u)));
        return All("d",Nat(),All("e",Nat(),Instance(Call("NeZero",e),
            All("U",MatrixOf(Product(Fin(d),Fin(e))),All("X",MatrixOf(Fin(d)),
                Eqn(Call("cHaarChannel",d,e,u,x),body))))));
    }
    private static Formula Moment()
    {
        Formula d=F.Id("d"),e=F.Id("e"),t=F.Id("t"),u=F.Id("U"),r=F.Id("r"),c=F.Id("c"),s=F.Id("s");
        Formula entry=Call("cHaarChannel",d,e,Call("val",u),
            QCall("Matrix.single",At(Proj(c,1),s),At(Proj(c,2),s),D(1)),
            At(Proj(r,1),s),At(Proj(r,2),s));
        Formula product=Seq(Prod,Underscore,Grp(s,Colon,Sp,Fin(t)),Sp,Parenthesized(entry));
        Formula integral=Seq(Int,Underscore,Grp(u,Colon,Sp,Unit(Product(Fin(d),Fin(e)))),Sp,
            Parenthesized(product),Sp,F.Id("d"),Parenthesized(Haar(Product(Fin(d),Fin(e)))));
        return All("d",Nat(),All("e",Nat(),All("t",Nat(),Instance(Call("NeZero",e),
            All("r",Index(d,t),All("c",Index(d,t),Eqn(Call("momentOp",d,e,t,r,c),integral)))))));
    }
    private static Formula Claim()
    {
        Formula d=F.Id("d"),e=F.Id("e"),t=F.Id("t"),k=F.Id("k"),j=F.Id("j");
        Formula conclusion=Leq(Call("hsNormSq",Pow(Call("momentOp",d,e,t),j)),
            Call("hsNormSq",Pow(Call("momentOp",d,e,t),k)));
        Formula body=All("d",Nat(),All("e",Nat(),All("t",Nat(),Instance(Call("NeZero",e),
            Implies(Leq(D(1),d),Implies(Leq(D(1),t),All("k",Nat(),All("j",Nat(),
                Implies(Leq(D(1),k),Implies(Leq(k,j),conclusion))))))))));
        return Eqn(Call("claim"),body);
    }
    private static Formula Norm()
    {
        Formula i=F.Id("i"),m=F.Id("M");
        Formula sum=Seq(Sum,Sp,Underscore,Grp(F.Id("r")),Sp,
            Seq(Sum,Sp,Underscore,Grp(F.Id("c")),Sp,
                QCall("Complex.normSq",At(m,F.Id("r"),F.Id("c")))));
        return All("i",F.Id("Type"),Instance(Call("Fintype",i),
            All("M",MatrixOf(i),Eqn(Call("hsNormSq",m),sum))));
    }
    private static Formula SwapHermitian() => Generic(QCall("Matrix.IsHermitian", SwapMatrix(F.Id("n"))));
    private static Formula SwapSquare()
    {
        Formula n = F.Id("n");
        Formula swap = SwapMatrix(n);
        return Generic(Eqn(Mul(swap, swap), Cast(D(1), MatrixOf(Product(n, n)))));
    }
    private static Formula SwapMatrix(Formula n) => At(
        Seq(Operatorname,Grp(F.Id("Equiv"),Dot,F.Id("Perm"),Dot,F.Id("permMatrix"))),
        Complex(), QCall("Equiv.prodComm", n, n));
    private static Formula Generic(Formula body) => All("n",F.Id("Type"),
        Instance(Call("Fintype",F.Id("n")), Instance(Call("DecidableEq",F.Id("n")), body)));
    private static Formula Nat() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Product(Formula x,Formula y) => Parenthesized(Seq(x,Sp,Times,Sp,y));
    private static Formula Index(Formula d,Formula t) => Product(Arrow(Fin(t),Fin(d)),Arrow(Fin(t),Fin(d)));
    private static Formula Arrow(Formula a,Formula b) => Parenthesized(Seq(a,Sp,To,Sp,b));
    private static Formula MatrixOf(Formula i) => Call("Matrix",i,i,Complex());
    private static Formula Unit(Formula i) => QCall("Matrix.unitaryGroup",i,Complex());
    private static Formula Haar(Formula i) => QCall("Measure.haarMeasure",Cast(Qualified("Top.top"),QCall("TopologicalSpace.PositiveCompacts",Unit(i))));
    private static Formula Qualified(string name)
    {
        var parts=name.Split('.');
        var tokens=new System.Collections.Generic.List<Formula>();
        for(int i=0;i<parts.Length;i++) { if(i>0) tokens.Add(Dot); tokens.Add(F.Id(parts[i])); }
        return Seq(Operatorname,Grp([..tokens]));
    }
    private static Formula QCall(string name,params Formula[] args) => At(Qualified(name),args);
    private static Formula At(Formula f,params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);
    private static Formula Cast(Formula f,Formula type) => Parenthesized(Seq(f,Colon,Sp,type));
    private static Formula Proj(Formula f,byte i) => Seq(Parenthesized(f),Dot,D(i));
    private static Formula Instance(Formula type,Formula body) => Seq(OpenBracket,type,CloseBracket,Sp,body);
    private static Formula All(string id,Formula type,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(id),type,body);
    private static Formula Lambda(string id,Formula body) => Seq(F.Id("fun"),Sp,F.Id(id),Sp,Mapsto,Sp,body);
    private static Formula Eqn(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Implies(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a,Formula b) => new Formula.Power(Parenthesized(a),b);
}
